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

`ifndef OVM_SEQUENCE_ITEM_SVH
`define OVM_SEQUENCE_ITEM_SVH

typedef class ovm_sequence_base;
typedef class ovm_sequencer_base;

class ovm_sequence_item extends ovm_transaction;

local      integer            m_sequence_id = -1;
protected  bit                m_use_sequence_info = 0;
protected  integer            m_depth = -1;
protected  ovm_sequencer_base m_sequencer = null;
protected  ovm_sequence_base  m_parent_sequence = null;
static     bit issued1=0,issued2=0;
bit        print_sequence_info = 0;

  function new (string             name = "ovm_sequence_item",
                ovm_sequencer_base sequencer = null,
                ovm_sequence_base  parent_sequence = null);
    super.new(name);
    if (sequencer != null) begin
      if (!issued1) begin
        issued1=1;
        ovm_report_warning("deprecated",
                           {"ovm_sequence_item::new()'s sequencer_ptr argument has been deprecated. ",
                            "The sequencer is now specified at the time a sequence is started ",
                            "using the start() task."});
      end
      m_sequencer = sequencer;
    end
    if (parent_sequence != null) begin
      if (!issued2) begin
        issued2=1;
        ovm_report_warning("deprecated",
          {"ovm_sequence_item::new()'s parent_sequence argument has been deprecated. ",
           "The parent sequence is now specified at the time a sequence is started ",
           "using the start() task."});
      end
      m_parent_sequence = parent_sequence;
    end
  endfunction // new

  function string get_type_name();
    return "ovm_sequence_item";
  endfunction 

  // Macro for factory creation
  `ovm_object_registry(ovm_sequence_item, "ovm_sequence_item")

  function void set_sequence_id(integer id);
    m_sequence_id = id;
  endfunction

  function integer get_sequence_id();
    return (m_sequence_id);
  endfunction

  function void set_use_sequence_info(bit value);
    m_use_sequence_info = value;
  endfunction

  function bit get_use_sequence_info();
    return (m_use_sequence_info);
  endfunction

  function void set_id_info(ovm_sequence_item item);
    assert (item != null) else begin
      ovm_report_fatal(get_full_name(), "set_id_info called with null parameter");
    end
    this.set_transaction_id(item.get_transaction_id());
    this.set_sequence_id(item.get_sequence_id());
  endfunction

  function void set_sequencer(ovm_sequencer_base sequencer);
    m_sequencer = sequencer;
    m_set_p_sequencer();
  endfunction // void

  function ovm_sequencer_base get_sequencer();
    return (m_sequencer);
  endfunction // ovm_sequencer_base

  function void set_parent_sequence(ovm_sequence_base parent);
    m_parent_sequence = parent;
  endfunction

  function ovm_sequence_base get_parent_sequence();
    return (m_parent_sequence);
  endfunction 

  function void set_depth(integer value);
    m_depth = value;
  endfunction

  function integer get_depth();

    // If depth has been set or calculated, then use that
    if (m_depth != -1) begin
      return (m_depth);
    end

    // Calculate the depth, store it, and return the value
    if (m_parent_sequence == null) begin
      m_depth = 1;
    end else begin
      m_depth = m_parent_sequence.get_depth() + 1;
    end

    return (m_depth);
  endfunction 

  virtual function bit is_item();
    return(1);
  endfunction

  virtual task start_item(ovm_sequence_item item, integer set_priority = -1);
    if(item == null)
      m_sequencer.ovm_report_fatal("NULLITM", {"attempting to start a null item from item/sequence '", get_full_name(), "'"});
    item.m_start_item(m_sequencer, this, set_priority);
  endtask  

  virtual task finish_item(ovm_sequence_item item, integer set_priority = -1);
    item.m_finish_item(item.get_sequencer(), this, set_priority);
  endtask // finish_item

  virtual task m_start_item(ovm_sequencer_base sequencer_ptr, ovm_sequence_item sequence_ptr,
                            integer set_priority);
    ovm_sequence_base this_seq;
    ovm_sequencer_base target_seqr;

    target_seqr = this.get_sequencer();
    
    if (target_seqr == null) begin
      ovm_report_fatal("STRITM", "sequence_item has null sequencer");
    end
    
    assert($cast(this_seq, sequence_ptr));
    target_seqr.wait_for_grant(this_seq, set_priority);
   if (target_seqr.recording_detail != OVM_NONE) begin
      void'(target_seqr.begin_tr(this, "aggregate items"));
    end
    sequence_ptr.pre_do(1);
  endtask  

  virtual task m_finish_item(ovm_sequencer_base sequencer_ptr, ovm_sequence_item sequence_ptr, integer set_priority = -1);
    ovm_sequence_base this_seq;
    ovm_sequencer_base target_seqr;

    target_seqr = this.get_sequencer();
    assert($cast(this_seq, sequence_ptr));
    sequence_ptr.mid_do(this);
    target_seqr.send_request(this_seq, this);
    target_seqr.wait_for_item_done(this_seq, -1);
    if (target_seqr.recording_detail != OVM_NONE) begin
      target_seqr.end_tr(this);
    end

    sequence_ptr.post_do(this);
  endtask // m_finish_item

// get_full_name
// -------------

  function string get_full_name();
    if(m_parent_sequence != null) 
      get_full_name = {m_parent_sequence.get_full_name(), "."};
    else if(m_sequencer!=null)
      get_full_name = {m_sequencer.get_full_name(), "."};
    if(get_name() != "") 
      get_full_name = {get_full_name, get_name()};
    else begin
      ovm_sequence_item tmp;
      tmp = this;
      $swrite(get_full_name, "%sitem_", get_full_name, tmp);
    end
  endfunction

// get_root_sequence_name
// --- 

  function string get_root_sequence_name();
    ovm_sequence_base root_seq;
    root_seq = get_root_sequence();
    if (root_seq == null)
      return "";
    else
      return root_seq.get_name();
  endfunction

  virtual function void m_set_p_sequencer();
    return;
  endfunction  

// get_root_sequence
// --- 

  function ovm_sequence_base get_root_sequence();
    ovm_sequence_item root_seq_base;
    ovm_sequence_base root_seq;
    root_seq_base = this;
    while(1) begin
      if(root_seq_base.get_parent_sequence()!=null) begin
        root_seq_base = root_seq_base.get_parent_sequence();
        $cast(root_seq, root_seq_base);
      end
      else
        return root_seq;
    end
  endfunction

// ovm_report_* should do this for the user for sequence messages!!!
// get_sequence_path
// -----------------

  function string get_sequence_path();
    ovm_sequence_item this_item;
    string seq_path;
    this_item = this;
    seq_path = this.get_name();
    while(1) begin
      if(this_item.get_parent_sequence()!=null) begin
        this_item = this_item.get_parent_sequence();
        seq_path = {this_item.get_name(), ".", seq_path};
      end
      else
        return seq_path;
    end
  endfunction

// do_print
// --------

  function void do_print (ovm_printer printer);
    string temp_str1;
    int depth = get_depth();
    super.do_print(printer);
    if(print_sequence_info || m_use_sequence_info) begin
      printer.print_field("depth", depth, $bits(depth), OVM_DEC, ".", "int");
      if(m_parent_sequence != null) begin
        temp_str1 = m_parent_sequence.get_full_name();
      end
      printer.print_string("parent sequence", temp_str1);
      temp_str1 = "";
      if(m_sequencer != null) begin
        temp_str1 = m_sequencer.get_full_name();
      end
      printer.print_string("sequencer", temp_str1);
    end
  endfunction

  ///////////////////////////////////////////////
  //
  //   Deprecated functions
  //
  ///////////////////////////////////////////////
     
  function void set_parent_seq(ovm_sequence_base parent);
    static bit issued=0;
    if (!issued) begin
      issued=1;
      ovm_report_warning("deprecated",
        {"ovm_sequence_item::set_parent_seq() has been deprecated and ",
        "replaced by set_parent_sequence()"});
    end
    set_parent_sequence(parent);
  endfunction

  function ovm_sequence_base get_parent_seq();
    static bit issued=0;
    if (!issued) begin
      issued=1;
      ovm_report_warning("deprecated",
        {"ovm_sequence_item::get_parent_seq() has been deprecated and ",
        "replaced by get_parent_sequence()"});
    end
    return(get_parent_sequence());
  endfunction // ovm_sequence_base

  virtual task pre_do(bit is_item);
    return;
  endtask // pre_body

  virtual task body();
    return;
  endtask  

  virtual function void mid_do(ovm_sequence_item this_item);
    return;
  endfunction
  
  virtual function void post_do(ovm_sequence_item this_item);
    return;
  endfunction

  virtual task wait_for_grant(integer item_priority = -1, bit  lock_request = 0);
    return;
  endtask

  virtual function void send_request(ovm_sequence_item request, bit rerandomize = 0);
    return;
  endfunction

  virtual task wait_for_item_done(integer transaction_id = -1);
    return;
  endtask // wait_for_item_done

endclass
`endif 
