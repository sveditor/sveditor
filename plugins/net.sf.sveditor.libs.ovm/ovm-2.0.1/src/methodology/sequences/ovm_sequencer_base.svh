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

typedef class ovm_sequencer_base;

typedef enum {SEQ_TYPE_REQ, SEQ_TYPE_LOCK, SEQ_TYPE_GRAB} SEQ_REQ_TYPE;
typedef enum {SEQ_ARB_FIFO, SEQ_ARB_WEIGHTED, SEQ_ARB_RANDOM, SEQ_ARB_STRICT_FIFO, SEQ_ARB_STRICT_RANDOM, SEQ_ARB_USER} 
        SEQ_ARB_TYPE;

class seq_req_class;
  static integer    g_request_id = 0;
  bit               grant;
  integer           sequence_id;
  integer           request_id;
  integer           item_priority;
  SEQ_REQ_TYPE      request;
  ovm_sequence_base sequence_ptr;

  function new(string name= "");
  endfunction
endclass  

class ovm_sequencer_base extends ovm_component;

  protected seq_req_class       arb_sequence_q[$];

  // The arb_completed associative array is used to indicate when a particular request_id
  // has been completed.  The array in indexed by request_id, and sequences will wait based
  // on the request_id assigned in the arb_sequence_q
  protected bit                 arb_completed[integer];

  protected ovm_sequence_base   lock_list[$];
  local     SEQ_ARB_TYPE        arbitration = SEQ_ARB_FIFO;
  local     ovm_sequence_base   reg_sequences[integer];
  local     static integer      g_sequence_id = 1;
  local     static integer      g_sequencer_id = 1;
  protected integer             m_sequencer_id;
  protected integer             m_lock_arb_size;  // used for waiting processes
  protected integer             m_arb_size;       // used for waiting processes
  protected integer             m_wait_for_item_sequence_id, m_wait_for_item_transaction_id;
            integer unsigned    pound_zero_count = 4;
  protected int                 m_seq_item_port_connect_size;

///// Copied from ovm_sequencer
  //set main and random sequence count variable if != -1
  //also accessed by ovm_main/random_sequence 
  integer count = -1;

  // testing fields
  integer m_random_count = 0;
  integer m_exhaustive_count = 0;
  integer m_simple_count = 0;

  //user settable property to limit main/random subsequences 
  //also accessed by ovm_main/random_sequence 
  integer unsigned max_random_count = 10;

  //Used for setting the maximum depth inside random sequences. 
  //(Beyond that depth, random creates only simple sequences.)
  int unsigned max_random_depth = 4;

  // This property defines which sequence will be auto-started (default=main).
  protected string default_sequence = "ovm_random_sequence";               

  // The sequeunce aray holds the type names of the sequence types registered
  // to this sequencer; the factory will actually create the instances on demand.
  string sequences[$];

  // The ids array associates each sequence entry (above) with an integer
  // number. This allows sequences to be randomly selected by randomizing
  // a number between 0 and the sequences array size.
  protected integer sequence_ids[string];

  // variable used to randomly select a sequence from the sequences array
  protected rand integer seq_kind;

///// End of Copied from ovm_sequencer

  
  ///////////////////////////////////////////////////
  
  function new (string name, ovm_component parent);
    super.new(name, parent);
    m_sequencer_id = g_sequencer_id++;
    m_lock_arb_size = -1;
    m_seq_item_port_connect_size = -1;
    void'(get_config_string("default_sequence", default_sequence));
    void'(get_config_int("count", count));
    void'(get_config_int("max_random_count", max_random_count));
    void'(get_config_int("max_random_depth", max_random_depth));
    void'(get_config_int("pound_zero_count", pound_zero_count));
  endfunction // new

  virtual function void build();
    super.build();
    void'(get_config_string("default_sequence", default_sequence));
    void'(get_config_int("count", count));
    void'(get_config_int("max_random_count", max_random_count));
    void'(get_config_int("max_random_depth", max_random_depth));
    void'(get_config_int("pound_zero_count", pound_zero_count));
  endfunction // build

  function void do_print (ovm_printer printer);
    super.do_print(printer);
    if(sequences.size() != 0) begin
      printer.print_string("default_sequence", default_sequence);
      printer.print_field("count", count, $bits(count), OVM_DEC);
      printer.print_field("max_random_count", max_random_count, 
        $bits(max_random_count), OVM_DEC);
      printer.print_array_header("sequences", sequences.size());
      for(int i=0; i<sequences.size(); ++i)
        printer.print_string($psprintf("[%0d]", i), sequences[i], "[");
      printer.print_array_footer();
      printer.print_field("max_random_depth", max_random_depth, 
        $bits(max_random_depth), OVM_DEC);
    end
  endfunction
 
  ///////////////////////////////////////////////////
  //
  // Local functions
  //
  ///////////////////////////////////////////////////

  protected function void m_update_lists();
    m_lock_arb_size++;
  endfunction // void

  function string display_queues();
    string s;
    
    $sformat(s, "  -- arb i/id/type: ");
    foreach (arb_sequence_q[i]) begin
      $sformat(s, "%s %0d/%0d/%s ", s, i, arb_sequence_q[i].sequence_id, arb_sequence_q[i].request);
    end // UNMATCHED !!
    $sformat(s, "%s\n -- lock_list i/id: ", s);
    foreach (lock_list[i]) begin
      $sformat(s, "%s %0d/%0d",s, i, lock_list[i].get_sequence_id());
    end // UNMATCHED !!
    return(s);
  endfunction // string

  local function integer next_sequence_id();
    return(g_sequence_id++);
  endfunction // int

  ///////////////////////////////////////////////////
  //
  // Local Sequence Registration Functions
  //
  ///////////////////////////////////////////////////

  protected virtual function int  m_find_number_driver_connections();
    return(0);
  endfunction

  protected function integer register_sequence(ovm_sequence_base sequence_ptr);

    if (sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1) > 0) begin
      return (sequence_ptr.get_sequence_id());
    end
    
    sequence_ptr.m_set_sqr_sequence_id(m_sequencer_id, next_sequence_id());
    reg_sequences[sequence_ptr.get_sequence_id()] = sequence_ptr;
    return(sequence_ptr.get_sequence_id());
  endfunction

  protected function ovm_sequence_base find_sequence(integer sequence_id);
    ovm_sequence_base seq_ptr;
    integer           i;
    
    // When sequence_id is -1, return the first available sequence.  This is used
    // when deleting all sequences
    if (sequence_id == -1) begin
      if (reg_sequences.first(i)) begin
        return(reg_sequences[i]);
      end
      return(null);
    end
    
    if (reg_sequences.exists(sequence_id) == 0) begin
//      ovm_report_warning("find_sequence", 
//                         $psprintf("Sequence %d doesn't exist (find_sequence)", sequence_id));
      return (null);
    end
    return(reg_sequences[sequence_id]);
  endfunction  

  protected function void unregister_sequence(integer sequence_id);
    if (reg_sequences.exists(sequence_id) == 0) begin
//      ovm_report_warning("unregister_sequence", 
//                         $psprintf("Sequence %d doesn't exist (unregister_sequence)", sequence_id));
    end
    reg_sequences.delete(sequence_id);
  endfunction  


  ///////////////////////////////////////////////////
  //
  // virtual function integer user_priority_arbitration(integer avail_sequences[$]);
  //
  // If a user specifies that the sequencer is to use user_priority_arbitration
  // through the call set_arbitration(SEQ_ARB_USER), then the sequencer will
  // call this function each time that it needs to arbitrate among sequences.
  //
  // This function must return an integer that matches one of the available
  // sequences that is passed into the call through the avail_sequences parameter
  //
  // Each integer in avail_sequences points to an entry in the arb_sequence_q, 
  // which is a protected queue that may be accessed from this function.
  //
  // To modify the operation of user_priority_arbitration, the function may
  // arbitrarily choose any sequence among the list of avail_sequences.  It is
  // important to choose only an available sequence.
  //
  // The default implementation is FIFO, which simply returns the first integer
  // in the avail_sequences array
  ///////////////////////////////////////////////////
  
  virtual function integer user_priority_arbitration(integer avail_sequences[$]);
    return (avail_sequences[0]);
  endfunction // user_priority_arbitration

  ///////////////////////////////////////////////////
  //
  // grant_queued_locks
  //    Any lock or grab requests that are at the front of the
  //    queue will be granted at the earliest possible time.
  //
  //    This function grants any queues at the front that are
  //    not locked out
  ///////////////////////////////////////////////////
  
  protected function void grant_queued_locks();
    integer i, temp;

    for (i = 0; i < arb_sequence_q.size(); i++) begin
      
      // Check for lock requests.  Any lock request at the head
      // of the queue that is not blocked will be granted immediately.
      temp = 0;
      if (i < arb_sequence_q.size()) begin
        if (arb_sequence_q[i].request == SEQ_TYPE_LOCK) begin
          temp = (is_blocked(arb_sequence_q[i].sequence_ptr) == 0);
        end
      end

      // Grant the lock request and remove it from the queue.
      // This is a loop to handle multiple back-to-back locks.
      // Since each entry is deleted, i remains constant
      while (temp) begin
        lock_list.push_back(arb_sequence_q[i].sequence_ptr);
        set_arbitration_completed(arb_sequence_q[i].request_id);
        arb_sequence_q.delete(i);
        m_update_lists();

        temp = 0;
        if (i < arb_sequence_q.size()) begin
          if (arb_sequence_q[i].request == SEQ_TYPE_LOCK) begin
            temp = is_blocked(arb_sequence_q[i].sequence_ptr) == 0;
          end
        end
      end
    end // for (i = 0; i < arb_sequence_q.size(); i++)
  endfunction // void

    
  ///////////////////////////////////////////////////
  //
  // choose_next_request
  //    When a driver requests an operation, this function
  //    must find the next available, unlocked, relevant sequence
  //
  //    This function returns -1 if no sequences are available
  //    or the entry into arb_sequence_q for the chosen sequence
  ///////////////////////////////////////////////////
  
  protected function integer choose_next_request();
    integer i, temp;
    integer avail_sequence_count;
    integer sum_priority_val;
    integer avail_sequences[$];
    integer highest_sequences[$];
    integer highest_pri;
    string  s;

    avail_sequence_count = 0;

    grant_queued_locks();

    for (i = 0; i < arb_sequence_q.size(); i++) begin
      // Search for available sequences.  If in SEQ_ARB_FIFO arbitration,
      // then just return the first available sequence.  Otherwise,
      // create a list for arbitration purposes.
      if (i < arb_sequence_q.size())
        if (arb_sequence_q[i].request == SEQ_TYPE_REQ)
          if (is_blocked(arb_sequence_q[i].sequence_ptr) == 0)
            if (arb_sequence_q[i].sequence_ptr.is_relevant() == 1) begin
              if (arbitration == SEQ_ARB_FIFO) begin
                return (i);
              end
              else avail_sequences.push_back(i);
            end
    end // for (i = 0; i < arb_sequence_q.size(); i++)

    // Return immediately if there are 0 or 1 available sequences
    if (arbitration == SEQ_ARB_FIFO) begin
      return (-1);
    end
    if (avail_sequences.size() < 1)  begin
      return (-1);
    end
    
    if (avail_sequences.size() == 1) begin
      return (avail_sequences[0]);
    end
    
    // If any locks are in place, then the available queue must
    // be checked to see if a lock prevents any sequence from proceeding
    if (lock_list.size() > 0) begin
      for (i = 0; i < avail_sequences.size(); i++) begin
        if (is_blocked(arb_sequence_q[avail_sequences[i]].sequence_ptr) != 0) begin
          avail_sequences.delete(i);
          i--;
        end
      end
      if (avail_sequences.size() < 1) return (-1);
      if (avail_sequences.size() == 1) return (avail_sequences[0]);
    end

    ///////////////////////////////////
    //  Weighted Priority Distribution
    ///////////////////////////////////
    if (arbitration == SEQ_ARB_WEIGHTED) begin
      sum_priority_val = 0;
      for (i = 0; i < avail_sequences.size(); i++) begin
        sum_priority_val += get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
      end
      
      // Pick an available sequence based on weighted priorities of available sequences
      temp = $urandom_range(sum_priority_val-1, 0);

      sum_priority_val = 0;
      for (i = 0; i < avail_sequences.size(); i++) begin
        if ((get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) + 
             sum_priority_val) > temp) begin
          return (avail_sequences[i]);
        end
        sum_priority_val += get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
      end
      ovm_report_fatal("Sequencer", "OVM Internal error in weighted arbitration code");
    end // if (arbitration == SEQ_ARB_WEIGHTED)
    
    ///////////////////////////////////
    //  Random Distribution
    ///////////////////////////////////
    if (arbitration == SEQ_ARB_RANDOM) begin
      i = $urandom_range(avail_sequences.size()-1, 0);
      return (avail_sequences[i]);
    end

    ///////////////////////////////////
    //  Strict Fifo
    ///////////////////////////////////
    if ((arbitration == SEQ_ARB_STRICT_FIFO) || arbitration == SEQ_ARB_STRICT_RANDOM) begin
      highest_pri = 0;
      // Build a list of sequences at the highest priority
      for (i = 0; i < avail_sequences.size(); i++) begin
        if (get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) > highest_pri) begin
          // New highest priority, so start new list
          `ovm_clear_queue(highest_sequences)
          highest_sequences.push_back(i);
          highest_pri = get_seq_item_priority(arb_sequence_q[avail_sequences[i]]);
        end
        else if (get_seq_item_priority(arb_sequence_q[avail_sequences[i]]) == highest_pri) begin
          highest_sequences.push_back(i);
        end
      end

      // Now choose one based on arbitration type
      if (arbitration == SEQ_ARB_STRICT_FIFO) begin
        return(highest_sequences[0]);
      end
      
      i = $urandom_range(highest_sequences.size()-1, 0);
      return (highest_sequences[i]);
    end // if ((arbitration == SEQ_ARB_STRICT_FIFO) || arbitration == SEQ_ARB_STRICT_RANDOM)

    if (arbitration == SEQ_ARB_USER) begin
      i = user_priority_arbitration(avail_sequences);

      // Check that the returned sequence is in the list of available sequences.  Failure to
      // use an available sequence will cause highly unpredictable results.
      highest_sequences = avail_sequences.find with (item == i);
      if (highest_sequences.size() == 0) begin
        ovm_report_fatal("Sequencer", $psprintf("Error in User arbitration, sequence %0d not available\n%s",
                                                i, display_queues()));
      end
      return(i);
    end
      
    ovm_report_fatal("Sequencer", "Internal error: Failed to choose sequence");

  endfunction // int

  protected task m_wait_arb_not_equal();
    wait (m_arb_size != m_lock_arb_size);
  endtask // m_wait_arb_not_equal

  protected task wait_for_available_sequence();
    integer i;
    integer is_relevant_entries[$];

    // This routine will wait for a change in the request list, or for
    // wait_for_relevant to return on any non-relevant, non-blocked sequence
    m_arb_size = m_lock_arb_size;

    for (i = 0; i < arb_sequence_q.size(); i++) begin
      if (arb_sequence_q[i].request == SEQ_TYPE_REQ) begin
        if (is_blocked(arb_sequence_q[i].sequence_ptr) == 0) begin
          if (arb_sequence_q[i].sequence_ptr.is_relevant() == 0) begin
            is_relevant_entries.push_back(i);
          end
        end
      end
    end

    // Typical path - don't need fork if all queued entries are relevant
    if (is_relevant_entries.size() == 0) begin
      m_wait_arb_not_equal();
      return;
    end

    fork  // isolate inner fork block for disabling
      begin
        fork
          begin
            fork

              // One path in fork is for any wait_for_relevant to return
              for(i = 0; i < is_relevant_entries.size(); i++) begin
                fork
                  begin
                    arb_sequence_q[is_relevant_entries[i]].sequence_ptr.wait_for_relevant();
                  end
                join_any
              end

              // The other path in the fork is for any queue entry to change
              begin
                m_wait_arb_not_equal();
              end
            join_any
          end
        join_any
        disable fork;
      end // fork
    join
  endtask // wait_for_available_sequence

  protected function integer get_seq_item_priority(seq_req_class seq_q_entry);
    // If the priority was set on the item, then that is used
    if (seq_q_entry.item_priority != -1) begin
      if (seq_q_entry.item_priority < 0) begin
        ovm_report_fatal("SEQITEMPRI", $psprintf("Sequence item from %s has illegal priority: %0d",
                                                 seq_q_entry.sequence_ptr.get_full_name(),
                                                 seq_q_entry.item_priority));
      end
      return (seq_q_entry.item_priority);
    end
    // Otherwise, use the priority of the calling sequence
    if (seq_q_entry.sequence_ptr.get_priority() < 0) begin
      ovm_report_fatal("SEQDEFPRI", $psprintf("Sequence %s has illegal priority: %0d",
                                               seq_q_entry.sequence_ptr.get_full_name(),
                                               seq_q_entry.sequence_ptr.get_priority()));
    end
    return (seq_q_entry.sequence_ptr.get_priority());
  endfunction
  
  ///////////////////////////////////////////////////
  //
  // arbitration completed tasks
  //    Used to tell the wait_for_grant function when
  //    a new arbitration is available
  ///////////////////////////////////////////////////
  
  task wait_for_arbitration_completed(integer request_id);
    int lock_arb_size;
    
    // Search the list of arb_wait_q, see if this item is done
    forever 
      begin
        lock_arb_size  = m_lock_arb_size;
        
        if (arb_completed.exists(request_id)) begin
          arb_completed.delete(request_id);
          return;
        end
        wait (lock_arb_size != m_lock_arb_size);
      end
  endtask // wait_for_arbitration_completed

  function void set_arbitration_completed(integer request_id);
    arb_completed[request_id] = 1;
  endfunction // void

///////////////////////////////////////////////////
//
// is_child
//    Determine if a scenario is a child of a parent
///////////////////////////////////////////////////

function bit is_child (ovm_sequence_base parent, ovm_sequence_base child);
    ovm_sequence_base sequence_ptr;

    if (child == null) begin
      ovm_report_fatal("ovm_sequencer", "is_child passed null child");
    end

    if (parent == null) begin
      ovm_report_fatal("ovm_sequencer", "is_child passed null parent");
    end

    sequence_ptr = child.get_parent_sequence();
    while (sequence_ptr != null) begin
      if (sequence_ptr.get_inst_id() == parent.get_inst_id()) begin
        return (1);
      end
      sequence_ptr = sequence_ptr.get_parent_sequence();
    end
    return (0);
endfunction // bit

  ///////////////////////////////////////////////////
  //
  // Methods available to Sequences
  // 
  ///////////////////////////////////////////////////
  
  virtual task wait_for_grant(ovm_sequence_base sequence_ptr, integer item_priority = -1, bit lock_request = 0);
    seq_req_class req_s;
    integer my_seq_id;

    if (sequence_ptr == null) begin
      ovm_report_fatal("ovm_sequencer", "wait_for_grant passed null sequence_ptr");
    end

    // Determine the number of drivers connected to this sequencer
    if(m_seq_item_port_connect_size < 0) begin
      m_seq_item_port_connect_size = m_find_number_driver_connections();
    end

`ifndef CDNS_NO_SQR_CON_CHK
    // If there are no drivers, then it is not possible to wait for grant
    if(m_seq_item_port_connect_size == 0) begin
      ovm_report_fatal("SQRWFG", "Wait_for_grant called on sequencer with no driver connected");
    end
`endif
    
    my_seq_id = register_sequence(sequence_ptr);
    
    // If lock_request is asserted, then issue a lock.  Don't wait for the response, since
    // there is a request immediately following the lock request
    if (lock_request == 1) begin
      req_s = new();
      req_s.grant = 0;
      req_s.sequence_id = my_seq_id;
      req_s.request = SEQ_TYPE_LOCK;
      req_s.sequence_ptr = sequence_ptr;
      req_s.request_id = req_s.g_request_id++;
      arb_sequence_q.push_back(req_s);
    end // lock_request == 1
        
    // Push the request onto the queue
    req_s = new();
    req_s.grant = 0;
    req_s.request = SEQ_TYPE_REQ;
    req_s.sequence_id = my_seq_id;
    req_s.item_priority = item_priority;
    req_s.sequence_ptr = sequence_ptr;
    req_s.request_id = req_s.g_request_id++;
    arb_sequence_q.push_back(req_s);
    m_update_lists();

    // Wait until this entry is granted
    // Continue to point to the element, since location in queue will change
    wait_for_arbitration_completed(req_s.request_id);

    // The wait_for_grant_semaphore is used only to check that send_request
    // is only called after wait_for_grant.  This is not a complete check, since
    // requests might be done in parallel, but it will catch basic errors
    req_s.sequence_ptr.m_wait_for_grant_semaphore++;

  endtask // wait_for_grant

  task wait_for_item_done(ovm_sequence_base sequence_ptr, integer transaction_id);
    integer sequence_id;

    sequence_id = sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1);
    m_wait_for_item_sequence_id = -1;
    m_wait_for_item_transaction_id = -1;

    if (transaction_id == -1) begin
      wait (m_wait_for_item_sequence_id == sequence_id);
    end else begin
      wait ((m_wait_for_item_sequence_id == sequence_id &&
             m_wait_for_item_transaction_id == transaction_id));
    end
  endtask // wait_for_item_done


///////////////////////////////////////////////////
//
//  function bit is_blocked(ovm_sequence_base sequence_ptr);
//
//  is_blocked will return 1 if the sequence refered to in the parameter
//  is currently locked out of the sequencer.  It will return 0 if the
//  sequence is currently allowed to issue operations
//
//  Note that even when a sequence is not blocked, it is possible
//  for another sequence to issue a lock before this sequence is able
//  to issue a request or lock
//
///////////////////////////////////////////////////
  
function bit is_blocked(ovm_sequence_base sequence_ptr);

    if (sequence_ptr == null)
      ovm_report_fatal("ovm_sequence_controller", "is_blocked passed null sequence_ptr");

      foreach (lock_list[i]) begin
        if ((lock_list[i].get_inst_id() != 
             sequence_ptr.get_inst_id()) &&
            (is_child(lock_list[i], sequence_ptr) == 0)) begin
          return (1);
        end
      end 
      return (0);
endfunction //


///////////////////////////////////////////////////
//
//  function bit is_locked(ovm_sequence_base sequence_ptr);
//
//  is_locked returns 1 if the sequence refered to in the parameter
//  currently has a lock on this sequencer.  It will return 0 if the
//  sequence does not currently have a lock.
// 
//  Note that even if this sequence has a lock, a child sequence may
//  also have a lock, in which case the sequence is still blocked from
//  issueing operations on the sequencer
//
///////////////////////////////////////////////////
  
function bit is_locked(ovm_sequence_base sequence_ptr);
    integer my_seq_id;
    
    if (sequence_ptr == null)
      ovm_report_fatal("ovm_sequence_controller", "is_locked passed null sequence_ptr");
    my_seq_id = register_sequence(sequence_ptr);
      foreach (lock_list[i]) begin
        if (lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) begin
          return (1);
        end
      end 
    return (0);
endfunction // bit

///////////////////////////////////////////////////
//
// lock_req
//    Internal Call by a sequence to request a lock.  Puts
//    the lock request onto the arbitration queue
///////////////////////////////////////////////////
  
local task lock_req(ovm_sequence_base sequence_ptr, bit lock);
    integer my_seq_id;
    seq_req_class new_req;
    
    if (sequence_ptr == null)
      ovm_report_fatal("ovm_sequence_controller", "lock_req passed null sequence_ptr");

    my_seq_id = register_sequence(sequence_ptr);
    new_req = new();
    new_req.grant = 0;
    new_req.sequence_id = sequence_ptr.get_sequence_id();
    new_req.request = SEQ_TYPE_LOCK;
    new_req.sequence_ptr = sequence_ptr;
    new_req.request_id = new_req.g_request_id++;
    
    if (lock == 1) begin
      // Locks are arbitrated just like all other requests
      arb_sequence_q.push_back(new_req);
    end else begin
      // Grabs are not arbitrated - they go to the front
      // TODO:
      // Missing: grabs get arbitrated behind other grabs
      arb_sequence_q.push_front(new_req);
      m_update_lists();
    end

    // If this lock can be granted immediately, then do so.
    grant_queued_locks();
    
    wait_for_arbitration_completed(new_req.request_id);
endtask
    
///////////////////////////////////////////////////
//
// unlock_req
//    Called by a sequence to request an unlock.  This
//    will remove a lock for this sequence if it exists
///////////////////////////////////////////////////
  
function void unlock_req(ovm_sequence_base sequence_ptr);
    integer my_seq_id;
    
    if (sequence_ptr == null) begin
      ovm_report_fatal("ovm_sequencer", "unlock_req passed null sequence_ptr");
    end
    my_seq_id = register_sequence(sequence_ptr);
    
    foreach (lock_list[i]) begin
      if (lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) begin
        lock_list.delete(i);
        m_update_lists();
        return;
      end
    end
endfunction // void

task lock(ovm_sequence_base sequence_ptr);
    lock_req(sequence_ptr, 1);
endtask // lock

task grab(ovm_sequence_base sequence_ptr);
    lock_req(sequence_ptr, 0);
endtask // lock

function void unlock(ovm_sequence_base sequence_ptr);
    unlock_req(sequence_ptr);
endfunction // lock

function void  ungrab(ovm_sequence_base sequence_ptr);
    unlock_req(sequence_ptr);
endfunction // lock

local function void remove_sequence_from_queues(ovm_sequence_base sequence_ptr);
    int i;
    int seq_id;
    
    seq_id = sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 0);
    
    // Remove all queued items for this sequence and any child sequences
    i = 0;
    do 
      begin
        if (arb_sequence_q.size() > i) begin
          if ((arb_sequence_q[i].sequence_id == seq_id) ||
              (is_child(sequence_ptr, arb_sequence_q[i].sequence_ptr))) begin
            arb_sequence_q.delete(i);
            m_update_lists();
          end
          else begin
            i++;
          end
        end
      end
    while (i < arb_sequence_q.size());
    
    // remove locks for this sequence, and any child sequences
    i = 0;
    do
      begin
        if (lock_list.size() > i) begin
          if ((lock_list[i].get_inst_id() == sequence_ptr.get_inst_id()) ||
              (is_child(sequence_ptr, lock_list[i]))) begin
            lock_list.delete(i);
            m_update_lists();
          end
          else begin
            i++;
          end
        end
      end
    while (i < lock_list.size());
    
    // Unregister the sequence_id, so that any returning data is dropped
    unregister_sequence(sequence_ptr.m_get_sqr_sequence_id(m_sequencer_id, 1));
endfunction // void

function void stop_sequences();
    ovm_sequence_base seq_ptr;
    
    // remove all sequences
    seq_ptr = find_sequence(-1);
    while (seq_ptr != null)
      begin
        kill_sequence(seq_ptr);
        seq_ptr = find_sequence(-1);
      end
endfunction // void
      
function void sequence_exiting(ovm_sequence_base sequence_ptr);
    remove_sequence_from_queues(sequence_ptr);
endfunction // void

function void kill_sequence(ovm_sequence_base sequence_ptr);
    integer i;

    remove_sequence_from_queues(sequence_ptr);
    // kill the sequence
    sequence_ptr.m_kill();
endfunction // void

virtual function bit is_grabbed();
    return(lock_list.size() != 0);
endfunction // bit

virtual function ovm_sequence_base current_grabber();
    if (lock_list.size() == 0) begin
      return (null);
    end
    return (lock_list[lock_list.size()-1]);
endfunction // ovm_sequence_base

  ///////////////////////////////////////////////////
  //
  // has_do_available function
  //   Determines if a sequence is ready to supply
  //   a transaction.  A sequence that obtains a
  //   transaction in pre-do must determine if the
  //   upstream object is ready to provide an item
  //
  //  returns 1 if a sequence is ready to issue an
  //  operation.  returns 0 if no unblocked, relevant
  //  sequence is requesting.
  //
  //////////////////////////////////////////////////

  function bit has_do_available();
    
    foreach (arb_sequence_q[i]) begin
      if (arb_sequence_q[i].sequence_ptr.is_relevant() == 1) begin
        return (1);
      end
    end // UNMATCHED !!
    return (0);
  endfunction
  
  ///////////////////////////////////////////////////
  //
  //  function void set_arbitration(SEQ_ARB_TYPE val);
  //
  //  Specify the arbitration mode for the sequencer.
  //  the arbitration mode must be one of:
  //
  //  SEQ_ARB_FIFO:          All requests are granted in FIFO order
  //  SEQ_ARB_WEIGHTED:      Requests are granted randomly by weight
  //  SEQ_ARB_RANDOM:        Requests are granted randomly
  //  SEQ_ARB_STRICT_FIFO:   All requests at the highest priority are granted
  //                         in fifo order
  //  SEQ_ARB_STRICT_RANDOM: All requests at the highest priority are granted
  //                         in random order
  //  SEQ_ARB_USER:          The user function user_priority_arbitration is
  //                         called.  That function will specify the next
  //                         sequence to grant.  The default user function 
  //                         specifies FIFO order
  //
  //////////////////////////////////////////////////

  function void set_arbitration(SEQ_ARB_TYPE val);
    arbitration = val;
  endfunction

  function SEQ_ARB_TYPE get_arbitration();
    return (arbitration);
  endfunction // SEQ_ARB_TYPE

  virtual function void analysis_write(ovm_sequence_item t);
    return;
  endfunction

  ///////////////////////////////////////////////////
  //
  // Methods available to Pull Drivers
  // 
  ///////////////////////////////////////////////////

  virtual task wait_for_sequences();
    for (int i = 0; i < pound_zero_count; i++) begin
      #0;
    end
  endtask // wait_for_sequences

   // add_sequence
// ------------

function void add_sequence(string type_name);

    //assign typename key to an int based on size
    //used with get_seq_kind to return an int key to match a type name
    sequence_ids[type_name] = sequences.size();
    //used w/ get_sequence to return a ovm_sequence factory object that 
    //matches an int id
    sequences.push_back(type_name);
endfunction

// remove_sequence
// ---------------

function void remove_sequence(string type_name);
  sequence_ids.delete(type_name);
  for (int i = 0; i < sequences.size(); i++) begin
    if (sequences[i] == type_name)
      sequences.delete(i);
  end
endfunction

// set_sequences_queue
// -------------------

function void set_sequences_queue(ref string sequencer_sequence_lib[$]);
    
    for(integer j=0; j < sequencer_sequence_lib.size(); j++) begin
      sequence_ids[sequencer_sequence_lib[j]] = sequences.size();
      this.sequences.push_back(sequencer_sequence_lib[j]);
    end
endfunction // void

// get_seq_kind
// ------------

// Return a unique sequence id given the name of a sequence.
// This id is expected to be used in inline constraints.
function integer get_seq_kind(string type_name);

  if (sequence_ids.exists(type_name))
    return sequence_ids[type_name];

  ovm_report_fatal("SEQNF", 
    $psprintf("Sequence type_name '%0s' not registered with this sequencer.",
    type_name));

endfunction


// get_sequence
// ------------

function ovm_sequence_base get_sequence(integer req_kind);

  ovm_factory factory = ovm_factory::get();
  ovm_sequence_base m_seq ;
  string m_seq_type;

  if (req_kind < 0 || req_kind >= sequences.size()) begin
    ovm_report_error("SEQRNG", 
      $psprintf("Kind arg '%0d' out of range. Need 0-%0d", 
      req_kind, sequences.size()-1));
  end

  m_seq_type = sequences[req_kind];
  if (!$cast(m_seq, factory.create_object_by_name(m_seq_type,
                                          get_full_name(),
                                          m_seq_type))) 
  begin
      ovm_report_fatal("FCTSEQ", 
        $psprintf("Factory can not produce a sequence of type %0s.",
        m_seq_type));
  end

  m_seq.print_sequence_info = 1;
  m_seq.set_sequencer (this);
  return m_seq;
  
endfunction // ovm_sequence_base

  function integer num_sequences();
    return (sequences.size());
  endfunction // num_sequences

  virtual function void send_request(ovm_sequence_base sequence_ptr, ovm_sequence_item t, bit rerandomize = 0);
    return;
  endfunction

///// End of Copied from ovm_sequencer

////////////////////////////////////////////////
//
// Deprecated Methods
//
////////////////////////////////////////////////

  virtual task start_sequence(ovm_sequence_base seq_base);
    static bit issued=0;
    if (!issued) begin
      issued=1;
      ovm_report_warning("deprecated",
        {"ovm_sequencer_base::start_sequence() has been deprecated and ",
        "replaced by the start() task, which becomes the only means ",
        "of starting sequences."});
    end

    fork
      seq_base.start(this);
    join_none
  endtask // start_sequence

endclass
