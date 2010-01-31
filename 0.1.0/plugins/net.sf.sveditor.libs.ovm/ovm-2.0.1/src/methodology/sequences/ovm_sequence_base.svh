//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

typedef enum {CREATED, PRE_BODY, BODY, POST_BODY, ENDED, STOPPED, FINISHED} ovm_sequence_state_enum;

class ovm_sequence_base extends ovm_sequence_item;

protected ovm_sequence_state_enum   m_sequence_state;
protected bit                       m_sequence_state_prebody, m_sequence_state_body, m_sequence_state_postbody;
protected bit                       m_sequence_state_ended, m_sequence_state_stopped;
          integer                   m_next_transaction_id = 1;
local     integer                   m_priority = -1;
event                               started, ended;
int                                 m_tr_handle;
int                                 m_wait_for_grant_semaphore;

// Each sequencer will assign a sequence id.  When a sequence is talking to multiple
// sequencers, each sequence_id is managed seperately
protected integer m_sqr_seq_ids[integer];

`ifndef INCA
protected process  m_sequence_process;
`else
protected bit m_sequence_started = 0;
protected event m_kill_event;
`endif
local bit                       m_use_response_handler = 0;

//used as an identifier in constraints for a specific type
rand integer unsigned seq_kind;

  // For user random selection. This excludes the exhaustive and
  // random sequences.
  constraint     pick_sequence { 
       (num_sequences() <= 2) || (seq_kind >= 2);
       (seq_kind <  num_sequences()) || (seq_kind == 0); }

  // bits to detect if is_relevant()/wait_for_relevant() are implemented
  local bit is_rel_default;
  local bit wait_rel_default;

  function new (string name = "ovm_sequence", 
                ovm_sequencer_base sequencer_ptr = null, 
                ovm_sequence_base parent_seq = null);
    static bit issued1=0,issued2=0;

    super.new(name);
    if (sequencer_ptr != null) begin
      if (!issued1) begin
        issued1=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence::new()'s sequencer_ptr argument has been deprecated. ",
          "The sequencer is now specified at the time a sequence is started ",
          "using the start() task."});
      end
    end
    if (parent_seq != null) begin
      if (!issued2) begin
        issued2=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence::new()'s parent_seq argument has been deprecated. ",
          "The parent sequence is now specified at the time a sequence is started ",
          "using the start() task."});
      end
    end
    m_sequence_state_prebody  = 0;
    m_sequence_state_body     = 0;
    m_sequence_state_postbody = 0;
    m_sequence_state_ended    = 0;
    m_sequence_state_stopped  = 0;
    m_sequence_state          = CREATED;
    m_wait_for_grant_semaphore = 0;
  endfunction // new

  function ovm_sequence_state_enum get_sequence_state();
    return (m_sequence_state);
  endfunction

  task wait_for_sequence_state(ovm_sequence_state_enum state);

    // Use state bits to ensure triggering even when there are no delta cycles between states
    case (state)
      PRE_BODY:  wait (m_sequence_state_prebody  == 1);
      BODY:      wait (m_sequence_state_body     == 1);
      POST_BODY: wait (m_sequence_state_postbody == 1);
      ENDED:     wait (m_sequence_state_ended    == 1);
      STOPPED:   wait (m_sequence_state_stopped  == 1);
      FINISHED:  wait (m_sequence_state == FINISHED);
    endcase // case(state)
  endtask // wait_for_sequence_state

  virtual task start (ovm_sequencer_base sequencer,
              ovm_sequence_base parent_sequence = null,
              integer this_priority = 100,
              bit call_pre_post = 1);
    
    m_parent_sequence = parent_sequence;
    m_sequencer       = sequencer;
    m_priority        = this_priority;
  endtask // start

  function void stop();
    return;
  endfunction

  virtual task pre_body();  
    return;
  endtask // pre_body

  virtual task post_body();
    return;
  endtask // post_body
    
  virtual task pre_do(bit is_item);
    return;
  endtask // pre_do

  virtual task body();
    ovm_report_warning("ovm_sequence_base", "Body definition undefined");
    return;
  endtask  

  virtual function bit is_item();
    return(0);
  endfunction

  virtual function void mid_do(ovm_sequence_item this_item);
    return;
  endfunction
  
  virtual function void post_do(ovm_sequence_item this_item);
    return;
  endfunction

  function integer num_sequences();
    if (m_sequencer == null) return (0);
    return (m_sequencer.num_sequences());
  endfunction // num_sequences

  function integer get_seq_kind(string type_name);
    if(m_sequencer)
      return m_sequencer.get_seq_kind(type_name);
    else 
      ovm_report_fatal("NULLSQ", $psprintf("%0s sequencer is null.",
                                           get_type_name()));
  endfunction

  function ovm_sequence_base get_sequence(integer unsigned req_kind);
    ovm_sequence_base m_seq;
    string m_seq_type;
    ovm_factory factory = ovm_factory::get();
    if (req_kind < 0 || req_kind >= m_sequencer.sequences.size()) begin
      ovm_report_error("SEQRNG", 
        $psprintf("Kind arg '%0d' out of range. Need 0-%0d",
        req_kind, m_sequencer.sequences.size()-1));
    end
    m_seq_type = m_sequencer.sequences[req_kind];
    if (!$cast(m_seq, factory.create_object_by_name(m_seq_type, get_full_name(), m_seq_type))) begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.",
        m_seq_type));
    end
    m_seq.set_use_sequence_info(1);
    return m_seq;
  endfunction // ovm_sequence_base

  function ovm_sequence_base get_sequence_by_name(string seq_name);
    ovm_sequence_base m_seq;
    if (!$cast(m_seq, factory.create_object_by_name(seq_name, get_full_name(), seq_name))) begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.", seq_name));
    end
    m_seq.set_use_sequence_info(1);
    return m_seq;
  endfunction // ovm_sequence_base

  task do_sequence_kind(integer unsigned req_kind);
    string m_seq_type;
    ovm_sequence_base m_seq;
    ovm_factory factory = ovm_factory::get();
    m_seq_type = m_sequencer.sequences[req_kind];
    if (!$cast(m_seq, factory.create_object_by_name(m_seq_type, get_full_name(), m_seq_type))) begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.", m_seq_type));
    end
    m_seq.set_use_sequence_info(1);
    m_seq.set_parent_sequence(this);
    m_seq.set_sequencer(m_sequencer);
    m_seq.set_depth(get_depth() + 1);
    m_seq.reseed();
    
    start_item(m_seq);
    assert(m_seq.randomize()) else begin
      ovm_report_warning("RNDFLD", "Randomization failed in do_sequence_kind()");
    end
    finish_item(m_seq);
  endtask // do_sequence_kind

  task create_and_start_sequence_by_name(string seq_name);
    ovm_sequence_base m_seq;
    m_seq = get_sequence_by_name(seq_name);
    m_seq.start(m_sequencer, this, this.get_priority(), 0);
  endtask

  function void set_priority (integer value);
    m_priority = value;
  endfunction

  function integer get_priority();
    return (m_priority);
  endfunction // int

  // wait_for_relevant
  // -----------------

  virtual task wait_for_relevant();
    event e;
    wait_rel_default = 1;
    if (is_rel_default != wait_rel_default)
      ovm_report_fatal("RELMSM", 
        "is_relevant() was implemented without defining wait_for_relevant()");
    @e;  // this is intended to never return
  endtask
 
  // is_relevant
  // -----------

  virtual function bit is_relevant(); 
    is_rel_default = 1;
    return 1;
  endfunction

  function bit is_blocked();
    return(m_sequencer.is_blocked(this));
  endfunction // bit

  task lock(ovm_sequencer_base sequencer = null);
    if (sequencer == null) begin
      assert (m_sequencer != null) else begin
        ovm_report_fatal("ISRELVNT", "Null m_sequencer reference");
      end
      m_sequencer.lock(this);
    end
    else begin
      sequencer.lock(this);
    end
  endtask // grab

  task grab(ovm_sequencer_base sequencer = null);
    if (sequencer == null) begin
      assert (m_sequencer != null) else begin
        ovm_report_fatal("GRAB", "Null m_sequencer reference");
      end
      m_sequencer.lock(this);
    end
    else begin
      sequencer.lock(this);
    end
  endtask // grab

  function void  unlock(ovm_sequencer_base sequencer = null);
    if (sequencer == null) begin
      assert (m_sequencer != null) else begin
        ovm_report_fatal("UNLOCK", "Null m_sequencer reference");
      end
      m_sequencer.unlock(this);
    end else begin
      sequencer.unlock(this);
    end
  endfunction

  function void  ungrab(ovm_sequencer_base sequencer = null);
    unlock(sequencer);
  endfunction // void

  virtual function void put_response (ovm_sequence_item response_item);
    return;
  endfunction // put_response

  virtual task m_start_item(ovm_sequencer_base sequencer_ptr, ovm_sequence_item sequence_ptr,
                            integer set_priority = -1);
    return;
  endtask  

  virtual task m_finish_item(ovm_sequencer_base sequencer_ptr, 
                             ovm_sequence_item sequence_ptr, 
                             integer set_priority = -1);
    ovm_sequence_base seq_base_ptr;

    assert($cast(seq_base_ptr, sequence_ptr)) else begin
        ovm_report_fatal("SEQMFINISH", "Failure to cast sequence item");
      end
    if (set_priority == -1) 
      begin
        if (get_priority() < 0) 
          begin
            start(sequencer_ptr, seq_base_ptr, 100, 0);
          end
        else 
          begin
            start(sequencer_ptr, seq_base_ptr, get_priority(), 0);
          end 
      end
    else 
      begin
        start(sequencer_ptr, seq_base_ptr, set_priority, 0);
      end
  endtask  

  virtual task wait_for_grant(integer item_priority = -1, bit lock_request = 0);
    assert (m_sequencer != null) else begin
      ovm_report_fatal("WAITGRANT", "Null m_sequencer reference");
    end
    m_sequencer.wait_for_grant(this, item_priority, lock_request);
  endtask // wait_for_grant

  virtual function void send_request(ovm_sequence_item request, bit rerandomize = 0);
    assert (m_sequencer != null) else begin
        ovm_report_fatal("SENDREQ", "Null m_sequencer reference");
      end
    m_sequencer.send_request(this, request, rerandomize);
  endfunction

  virtual task wait_for_item_done(integer transaction_id = -1);
    assert (m_sequencer != null) else begin
        ovm_report_fatal("WAITITEMDONE", "Null m_sequencer reference");
      end
    m_sequencer.wait_for_item_done(this, transaction_id);
  endtask // wait_for_item_done

  virtual function void set_sequencer(ovm_sequencer_base sequencer);
    m_sequencer = sequencer;
  endfunction // void

  virtual function ovm_sequencer_base get_sequencer();
    return(m_sequencer);
  endfunction // ovm_sequencer_base

  function void m_kill();
`ifndef INCA
    if (m_sequence_process != null) begin
      m_sequence_process.kill;
      m_sequence_process = null;
    end
`else
    ->m_kill_event;
    m_sequence_started=0;
`endif
    m_sequence_state = STOPPED;
    m_sequence_state_stopped = 1;
  endfunction // void

  function void kill();
`ifndef INCA
    if (m_sequence_process != null) begin
`else
    if (m_sequence_started != 0) begin
`endif
      // If we are not connected to a sequencer, then issue
      // kill locally.
      if (m_sequencer == null) begin
        m_kill();
        return;
      end
      // If we are attached to a sequencer, then the sequencer
      // will clear out queues, and then kill this sequence
      m_sequencer.kill_sequence(this);
      return;
    end
  endfunction // void

  function void use_response_handler(bit enable);
    m_use_response_handler = enable;
  endfunction // void

  function bit get_use_response_handler();
    return(m_use_response_handler);
  endfunction // bit

  virtual function void response_handler(ovm_sequence_item response);
    return;
  endfunction // response_handler

  protected function ovm_sequence_item create_item(ovm_object_wrapper type_var, 
                                                   ovm_sequencer_base l_sequencer, string name);

  ovm_factory f_ = ovm_factory::get();
  $cast(create_item,  f_.create_object_by_type( type_var, this.get_full_name(), name ));

  create_item.set_use_sequence_info(1);
  create_item.set_parent_sequence(this);
  create_item.set_sequencer(l_sequencer);
  create_item.set_depth(get_depth() + 1);
  create_item.reseed();

  endfunction // ovm_sequence_item

  function integer m_get_sqr_sequence_id(integer sequencer_id, bit update_sequence_id);
    if (m_sqr_seq_ids.exists(sequencer_id)) begin
      if (update_sequence_id == 1) begin
        set_sequence_id(m_sqr_seq_ids[sequencer_id]);
      end
      return(m_sqr_seq_ids[sequencer_id]);
    end
    else begin
      if (update_sequence_id == 1) begin
        set_sequence_id(-1);
      end
      return(-1);
    end
  endfunction
  
  function void m_set_sqr_sequence_id(integer sequencer_id, integer sequence_id);
    m_sqr_seq_ids[sequencer_id] = sequence_id;
    set_sequence_id(sequence_id);
  endfunction // void

////////////////////////////////////////////////
//
// OVM Layered stimulus backward compatibility
//
////////////////////////////////////////////////

  function integer get_id();
    return (get_sequence_id());
  endfunction // get_id

  function ovm_sequence_base get_parent_scenario();
    return (m_parent_sequence);
  endfunction // ovm_sequence_base

virtual task pre_apply();
    return;
endtask

virtual task mid_apply();
    return;
endtask

virtual task post_apply();
    return;
endtask // post_apply

endclass                

