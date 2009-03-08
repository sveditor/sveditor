// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_event.svh#8 $
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

`ifndef OVM_EVENT_SVH
`define OVM_EVENT_SVH

typedef class ovm_object;
typedef class ovm_event;

//------------------------------------------------------------------------------
//
// CLASS: ovm_event_callback
//
// callbacks for ovm_event objects- users should inherit and override one or
// more of the methods
//
//------------------------------------------------------------------------------

virtual class ovm_event_callback extends ovm_object;
  extern         function            new          (string name=""); 
  extern virtual function ovm_object create       (string name=""); 
  extern virtual function bit        pre_trigger  (ovm_event e, ovm_object data=null);
  extern virtual function void       post_trigger (ovm_event e, ovm_object data=null);
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_event
//
//------------------------------------------------------------------------------

class ovm_event extends ovm_object;

  const static string type_name = "ovm_event";

  extern         function              new               (string name="");
  extern virtual function ovm_object   create            (string name=""); 
  extern virtual function string       get_type_name     ();

  // waiting
  extern virtual task                  wait_on           (bit delta=0);
  extern virtual task                  wait_off          (bit delta=0);
  extern virtual task                  wait_trigger      ();
  extern virtual task                  wait_ptrigger     ();
  extern virtual task                  wait_trigger_data (output ovm_object data);
  extern virtual task                  wait_ptrigger_data(output ovm_object data);

  // triggering
  extern virtual function void         trigger           (ovm_object data=null);
  extern virtual function ovm_object   get_trigger_data  ();
  extern virtual function time         get_trigger_time  ();

  // state
  extern virtual function bit          is_on             ();
  extern virtual function bit          is_off            ();
  extern virtual function void         reset             (bit wakeup=0);

  // callbacks
  extern virtual function void         add_callback      (ovm_event_callback cb,
                                               bit append=1);
  extern virtual function void         delete_callback   (ovm_event_callback cb);

  // waiters list
  extern virtual function void         cancel            ();
  extern virtual function int          get_num_waiters   ();


  local event      m_event;
  local int        num_waiters;
  local bit        on;
  local time       trigger_time=0;
  local ovm_object trigger_data;
  local ovm_event_callback  callbacks[$];

  extern virtual function void do_print (ovm_printer printer);
  extern virtual function void do_copy (ovm_object rhs);

endclass



//------------------------------------------------------------------------------
//
// CLASS: ovm_event_pool
//
//------------------------------------------------------------------------------

class ovm_event_pool extends ovm_object;

  const static string type_name = "ovm_event_pool";

  extern         function                  new             (string name="");
  extern virtual function ovm_object       create          (string name=""); 
  extern virtual function string           get_type_name   ();

  extern static  function ovm_event_pool   get_global_pool ();

  extern virtual function ovm_event        get             (string name);

  extern virtual function int              num             ();
  extern virtual function void             delete          (string name);
  extern virtual function int              exists          (string name);
  extern virtual function int              first           (ref string name);
  extern virtual function int              last            (ref string name);
  extern virtual function int              next            (ref string name);
  extern virtual function int              prev            (ref string name);

  static local ovm_event_pool  m_global_pool;
  local  ovm_event              pool[string];

  extern virtual function void do_print (ovm_printer printer);
  extern virtual function void do_copy (ovm_object rhs);

endclass



//-----------------------------------------------------------------------------
//
// CLASS: ovm_barrier
//
//-----------------------------------------------------------------------------

class ovm_barrier extends ovm_object;

  const static string type_name = "ovm_barrier";

  extern          function               new             (string name="",
                                                          int threshold=0);
  extern virtual  function ovm_object    create          (string name=""); 
  extern virtual  function string        get_type_name   ();

  extern virtual  task                   wait_for        ();
  extern virtual  function void          reset           (bit wakeup=1);
  extern virtual  function void          set_auto_reset  (bit value=1);
  extern virtual  function void          set_threshold   (int threshold);
  extern virtual  function int           get_threshold   ();
  extern virtual  function int           get_num_waiters ();
  extern virtual  function void          cancel          ();

  // private
  extern local function bit            reached_threshold ();

  local  int           threshold;
  local  int           num_waiters;
  local  bit           at_threshold;
  local  bit           auto_reset;
  local  ovm_event     m_event;

  extern local task m_trigger();

  extern virtual function void do_print (ovm_printer printer);
  extern virtual function void do_copy (ovm_object rhs);

endclass



//------------------------------------------------------------------------------
//
// CLASS: ovm_barrier_pool
//
//------------------------------------------------------------------------------

class ovm_barrier_pool extends ovm_object; 

  const static string type_name = "ovm_barrier_pool";

  extern         function                  new             (string name="");
  extern virtual function ovm_object       create          (string name=""); 
  extern virtual function string           get_type_name   ();

  extern static function ovm_barrier_pool  get_global_pool ();

  extern virtual function ovm_barrier      get             (string name);
  extern virtual function int              num             ();
  extern virtual function void             delete          (string name);
  extern virtual function int              exists          (string name);
  extern virtual function int              first           (ref string name);
  extern virtual function int              last            (ref string name);
  extern virtual function int              next            (ref string name);
  extern virtual function int              prev            (ref string name);

  static local ovm_barrier_pool  m_global_pool;
  local  ovm_barrier       pool[string];

  extern virtual function void do_print (ovm_printer printer);
  extern virtual function void do_copy (ovm_object rhs);

endclass


`endif // OVM_EVENT_SVH

