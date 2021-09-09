//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
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


//------------------------------------------------------------------------------
//
// CLASS: ovm_sequence #(REQ,RSP)
//
// The ovm_sequence class provides the interfaces necessary in order to create
// streams of sequence items and/or other sequences.
//
//------------------------------------------------------------------------------

virtual class ovm_sequence #(type REQ = ovm_sequence_item,
                             type RSP = REQ) extends ovm_sequence_base;

typedef ovm_sequencer_param_base #(REQ, RSP) sequencer_t;

sequencer_t        param_sequencer;
REQ                req;
RSP                rsp;
local RSP          response_queue[$];
protected int      response_queue_depth = 8;
protected bit      response_queue_error_report_disabled = 0;


  // Function: new
  //
  // Creates and initializes a new sequence object.
  //
  // The ~sequencer_ptr~ and ~parent_seq~ arguments are deprecated in favor of
  // their being set in the start method.  

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
          "using the start() task."}, OVM_NONE);
      end
      m_sequencer = sequencer_ptr;
    end
    if (parent_seq != null) begin
      if (!issued2) begin
        issued2=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence::new()'s parent_seq argument has been deprecated. ",
          "The parent sequence is now specified at the time a sequence is started ",
          "using the start() task."}, OVM_NONE);
      end
      m_parent_sequence = parent_seq;
    end
  endfunction // new

  function void do_print (ovm_printer printer);
    super.do_print(printer);
    printer.print_object("req", req);
    printer.print_object("rsp", rsp);
  endfunction

  
  // Task: start
  //
  // The start task is called to begin execution of a sequence.
  //
  // The ~sequencer~ argument specifies the sequencer on which to run this
  // sequence. The sequencer must be compatible with the sequence.
  //
  // If ~parent_sequence~ is null, then the sequence is a parent, otherwise it is
  // a child of the specified parent.
  //
  // By default, the ~priority~ of a sequence is 100. A different priority may be
  // specified by this_priority. Higher numbers indicate higher priority.
  //
  // If ~call_pre_post~ is set to 1, then the pre_body and post_body tasks will be
  // called before and after the sequence body is called.

  virtual task start (ovm_sequencer_base sequencer,
              ovm_sequence_base parent_sequence = null,
              integer this_priority = 100,
              bit call_pre_post = 1);

    m_sequence_state_prebody  = 0;
    m_sequence_state_body     = 0;
    m_sequence_state_postbody = 0;
    m_sequence_state_ended    = 0;
    m_sequence_state_stopped  = 0;

    if ((this_priority < 1) |  (^this_priority === 1'bx)) begin
      ovm_report_fatal("SEQPRI", $psprintf("Sequence %s start has illegal priority: %0d",
                                           get_full_name(),
                                           this_priority), OVM_NONE);
      end

    // Check that the response queue is empty from earlier runs
    `ovm_clear_queue(response_queue);

    super.start(sequencer, parent_sequence, this_priority, call_pre_post);
    m_set_p_sequencer();

    if (m_sequencer != null) begin
        if (m_parent_sequence == null) begin
          m_tr_handle = m_sequencer.begin_tr(this, get_name());
        end else begin
          m_tr_handle = m_sequencer.begin_child_tr(this, m_parent_sequence.m_tr_handle, 
                                                   get_root_sequence_name());
        end
    end

    // Ensure that the sequence_id is intialized in case this sequence has been stopped previously
    set_sequence_id(-1);
    // Remove all sqr_seq_ids
    m_sqr_seq_ids.delete();

    // Register the sequence with the sequencer if defined.
    if (m_sequencer != null) begin
      void'(m_sequencer.register_sequence(this));
    end
    
    ->started;
    
    if (call_pre_post == 1) begin
      m_sequence_state = PRE_BODY;
      m_sequence_state_prebody = 1;
      #0;   // Allow external waiter to be activated
      this.pre_body();
    end

    if (parent_sequence != null) begin
      parent_sequence.pre_do(0);
      parent_sequence.mid_do(this);
    end

    m_sequence_state = BODY;
    m_sequence_state_body = 1;
    #0;   // Allow external waiter to be activated
    
`ifndef INCA
    
    fork
      begin
        m_sequence_process = process::self();
        body();
        m_sequence_state_ended = 1;
        m_sequence_state = ENDED;
        #0;   // Allow external waiter to be activated
      end
    join
    
`else
    
    fork //wrap the fork/join_any to only effect this block
      begin
        fork
          begin
            body();
            m_sequence_state_ended = 1;
            m_sequence_state = ENDED;
          end
          begin
            m_sequence_started = 1;
            @(m_kill_event or m_sequence_state==ENDED);
          end
        join_any
        if(m_sequence_state!=ENDED) begin
          disable fork;
        end
        else
          #0;   // Allow external waiter to be activated
      end
    join
        
`endif
        
    if (parent_sequence != null) begin
      parent_sequence.post_do(this);
    end

    if (call_pre_post == 1) begin
      m_sequence_state = POST_BODY;
      m_sequence_state_postbody = 1;
      #0;   // Allow external waiter to be activated
      post_body();
    end

    ->ended;
    m_sequence_state = FINISHED;

    if (m_sequencer != null) begin      
        m_sequencer.end_tr(this);
    end

    // Clean up any sequencer queues after exiting
    if (m_sequencer != null) begin
      m_sequencer.sequence_exiting(this);
    end
  endtask // start


  // Function: send_request
  //
  // This method will send the request item to the sequencer, which will forward
  // it to the driver.  If the rerandomize bit is set, the item will be
  // randomized before being sent to the driver. The send_request function may
  // only be called after <ovm_sequence_base::wait_for_grant> returns.

  function void send_request(ovm_sequence_item request, bit rerandomize = 0);
    REQ m_request;
    
    if (m_sequencer == null) begin
      ovm_report_fatal("SSENDREQ", "Null m_sequencer reference", OVM_NONE);
    end
    if (!$cast(m_request, request)) begin
      ovm_report_fatal("SSENDREQ", "Failure to cast ovm_sequence_item to request", OVM_NONE);
    end
    m_sequencer.send_request(this, m_request, rerandomize);
  endfunction // void


  // Function: get_current_item
  //
  // Returns the request item currently being executed by the sequencer. If the
  // sequencer is not currently executing an item, this method will return null.
  //
  // The sequencer is executing an item from the time that get_next_item or peek
  // is called until the time that get or item_done is called.
  //
  // Note that a driver that only calls get will never show a current item,
  // since the item is completed at the same time as it is requested.

  function REQ get_current_item();
    if (!$cast(param_sequencer, m_sequencer))
      ovm_report_fatal("SGTCURR", "Failure to cast m_sequencer to the parameterized sequencer", OVM_NONE);
    return (param_sequencer.get_current_item());
  endfunction // REQ


  // Task: get_response
  //
  // By default, sequences must retrieve responses by calling get_response.
  // If no transaction_id is specified, this task will return the next response
  // sent to this sequence.  If no response is available in the response queue,
  // the method will block until a response is recieved.
  //
  // If a transaction_id is parameter is specified, the task will block until
  // a response with that transaction_id is received in the response queue.
  //
  // The default size of the response queue is 8.  The get_response method must
  // be called soon enough to avoid an overflow of the response queue to prevent
  // responses from being dropped.
  //
  // If a response is dropped in the response queue, an error will be reported
  // unless the error reporting is disabled via
  // set_response_queue_error_report_disabled.

  task get_response(output RSP response, input int transaction_id = -1);
    int queue_size, i;

    if (response_queue.size() == 0) begin
      wait (response_queue.size() != 0);
    end

    if (transaction_id == -1) begin
      response = response_queue.pop_front();
      return;
    end

    forever begin
      queue_size = response_queue.size();
      for (i = 0; i < queue_size; i++) begin
        if (response_queue[i].get_transaction_id() == transaction_id) 
          begin
            response = response_queue[i];
            response_queue.delete(i);
            return;
          end
      end
      wait (response_queue.size() != queue_size);
    end
  endtask // get_response


  // Function: set_sequencer
  // 
  // Sets the default sequencer for the sequence to sequencer.  It will take
  // effect immediately, so it should not be called while the sequence is
  // actively communicating with the sequencer.

  virtual function void set_sequencer(ovm_sequencer_base sequencer);
    m_sequencer = sequencer;
    m_set_p_sequencer();
  endfunction // void

 
  // Function: set_response_queue_error_report_disabled
  //
  // By default, if the response_queue overflows, an error is reported. The
  // response_queue will overflow if more responses are sent to this sequence
  // from the driver than get_response calls are made. Setting value to 0
  // disables these errors, while setting it to 1 enables them.

  function void set_response_queue_error_report_disabled(bit value);
    response_queue_error_report_disabled = value;
    endfunction

  
  // Function: get_response_queue_error_report_disabled
  //
  // When this bit is 0 (default value), error reports are generated when
  // the response queue overflows. When this bit is 1, no such error
  // reports are generated.

  function bit get_response_queue_error_report_disabled();
    return(response_queue_error_report_disabled);
  endfunction // bit


  // Function: set_response_queue_depth
  //
  // The default maximum depth of the response queue is 8. These method is used
  // to examine or change the maximum depth of the response queue.
  //
  // Setting the response_queue_depth to -1 indicates an arbitrarily deep
  // response queue.  No checking is done.

  function void set_response_queue_depth(int value);
    response_queue_depth = value;
  endfunction  


  // Function: get_response_queue_depth
  //
  // Returns the current depth setting for the response queue.

  function int get_response_queue_depth();
    return(response_queue_depth);
  endfunction  


  // Function- put_response
  //
  // Internal method.

  virtual function void put_response(ovm_sequence_item response_item);
    RSP response;

    if (!$cast(response, response_item)) begin
      ovm_report_fatal("PUTRSP", "Failure to cast response in put_response", OVM_NONE);
    end
    if ((response_queue_depth == -1) ||
        (response_queue.size() < response_queue_depth)) begin
      response_queue.push_back(response);
      return;
    end
    if (response_queue_error_report_disabled == 0) begin
      ovm_report_error(get_full_name(), "Response queue overflow, response was dropped", OVM_NONE);
    end
  endfunction // put_response

endclass
