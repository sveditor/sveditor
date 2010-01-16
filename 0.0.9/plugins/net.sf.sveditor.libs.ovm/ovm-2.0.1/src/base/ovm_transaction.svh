// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_transaction.svh#5 $
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

`ifndef OVM_TRANSACTION_SVH
`define OVM_TRANSACTION_SVH

`include "base/ovm_object.svh"

typedef class ovm_event;
typedef class ovm_event_pool;
typedef class ovm_component;
    
//------------------------------------------------------------------------------
//
// CLASS: ovm_transaction
//
// The base class transactions class
//
//------------------------------------------------------------------------------
    
virtual class ovm_transaction extends ovm_object;

  //For a transaction, the parent is the initiator of the transaction
  extern function        new            (string name="", 
                                         ovm_component initiator=null);

  extern function void          set_initiator  (ovm_component initiator);
  extern function ovm_component get_initiator  ();

  //Transaction interface
  extern function void    accept_tr         (time accept_time=0);
  extern function integer begin_tr          (time begin_time=0);
  extern function integer begin_child_tr    (time begin_time=0, 
                                             integer parent_handle=0);
  extern function void    end_tr            (time end_time=0, bit free_handle=1);

  extern function integer get_tr_handle     ();
  extern function void    disable_recording ();
  extern function void    enable_recording  (string stream);
  extern function bit     is_recording_enabled();
  extern function bit     is_active         ();

  //Methods to add action to transaction interface
  extern virtual protected function void   do_accept_tr      ();
  extern virtual protected function void   do_begin_tr       ();
  extern virtual protected function void   do_end_tr         ();

  //Access methods
  extern function ovm_event_pool get_event_pool ();
  extern function time   get_begin_time     ();
  extern function time   get_end_time       ();
  extern function time   get_accept_time    ();

  //Override data control methods for internal properties
  extern virtual function void do_print (ovm_printer printer);
  extern virtual function void do_record (ovm_recorder recorder);
  extern virtual function void do_copy (ovm_object rhs);

  //protected ovm_events  m_events;

  extern protected function integer m_begin_tr (time    begin_time=0, 
                                                integer parent_handle=0,
                                                bit     has_parent=0);

  local time             begin_time=-1;
  local time             end_time=-1;
  local time             accept_time=-1;

  local ovm_component    initiator;
  local integer          stream_handle;
  local integer          tr_handle;      
  local bit              record_enable = 0;

  local ovm_event_pool   m_event_pool = new;

  local integer m_transaction_id = 0;
  extern function void               set_transaction_id(integer id);
  extern function integer            get_transaction_id();
       
  extern virtual function string convert2string;

endclass

`endif  //OVM_TRANSACTION_SVH
