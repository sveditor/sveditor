// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_event.sv#16 $
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

`include "base/ovm_event.svh"


//------------------------------------------------------------------------------
//
// CLASS: ovm_event_callback
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_event_callback::new (string name=""); 
  super.new(name);
endfunction


// create
// ------

function ovm_object ovm_event_callback::create (string name="");
  ovm_event_callback v;
// Not allowed since ovm_event_callback is abstract 
//  v=new(name);
//  return v;
  return null;
endfunction


// pre_trigger
// -----------

function bit ovm_event_callback::pre_trigger(ovm_event e,
                                             ovm_object data=null);
  // empty by default
  return 0;
endfunction


// post_trigger
// ------------

function void ovm_event_callback::post_trigger(ovm_event e,
                                               ovm_object data=null);
  // empty by default
  return;
endfunction


//------------------------------------------------------------------------------
//
// CLASS: ovm_event
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_event::new (string name=""); 
  super.new(name);
endfunction


// get_type_name
// -------------

function string ovm_event::get_type_name ();
  return this.type_name;
endfunction


// create
// ------

function ovm_object ovm_event::create (string name=""); 
  ovm_event v;
  v=new(name);
  return v;
endfunction


// wait_on
// -------

task ovm_event::wait_on (bit delta=0);

  if (this.on) begin
    if (delta)
      #0;
    return;
  end
  this.num_waiters++;
  @on; //wait(m_event.triggered); //@on; 'this' not allowed
endtask


// wait_off
// --------

task ovm_event::wait_off (bit delta=0);

  if (!this.on) begin
    if (delta)
      #0;
    return;
  end
  this.num_waiters++;
  @on;
endtask


// wait_trigger
// ------------

task ovm_event::wait_trigger ();
  this.num_waiters++;
  @m_event;
endtask

// wait_trigger_data
// -----------------

task ovm_event::wait_trigger_data (output ovm_object data);
  wait_trigger();
  data = get_trigger_data();
endtask


// wait_ptrigger
// -------------

task ovm_event::wait_ptrigger ();
  if (m_event.triggered)
    return;
  this.num_waiters++;
  @m_event;
endtask

// wait_ptrigger_data
// -----------------

task ovm_event::wait_ptrigger_data (output ovm_object data);
  wait_ptrigger();
  data = get_trigger_data();
endtask


// trigger
// -------

function void ovm_event::trigger (ovm_object data=null);
  int skip;
  skip=0;
  if (this.callbacks.size()) begin
    for (int i=0;i<callbacks.size();i++) begin
      ovm_event_callback tmp;
      tmp=this.callbacks[i];
      skip = skip + tmp.pre_trigger(this,data);
    end
  end
  if (skip==0) begin
    ->m_event;
    if (this.callbacks.size()) begin
      for (int i=0;i<this.callbacks.size();i++) begin
        ovm_event_callback tmp;
        tmp=this.callbacks[i];
        tmp.post_trigger(this,data);
      end
    end
    this.num_waiters = 0;
    this.on = 1;
    this.trigger_time = $time;
    this.trigger_data = data;
  end
  //return 1; no timeout yet, so don't need
endfunction


// get_trigger_data
// ----------------

function ovm_object ovm_event::get_trigger_data ();
  return this.trigger_data;
endfunction


// get_trigger_time
// ----------------

function time ovm_event::get_trigger_time ();
  return this.trigger_time;
endfunction



/*
// is_triggered
// ------------

function bit ovm_event::is_triggered ();
  // TODO: need independent process to reset this
  if ($time == 0)
    return 0;
  return (this.trigger_time >= $time);
endfunction


// is_pending
// ----------

function void ovm_event::is_pending ();
  // TODO: need independent process to reset this
  if ($time == 0)
    return 0;
  return (this.trigger_time <= $time);
endfunction
*/


// is_on
// -----

function bit ovm_event::is_on ();
  return (this.on == 1);
endfunction


// is_off
// ------

function bit ovm_event::is_off ();
  return (this.on == 0);
endfunction


// reset
// -----

function void ovm_event::reset (bit wakeup=0);
  event e;
  if (wakeup)
    ->m_event;
  m_event = e;
  this.num_waiters = 0;
  on = 0;
  trigger_time = 0;
  trigger_data = null;
endfunction


// cancel
// ------

function void ovm_event::cancel ();
  if (this.num_waiters > 0)
    this.num_waiters--;
endfunction


// get_num_waiters
// ---------------

function int ovm_event::get_num_waiters ();
  return this.num_waiters;
endfunction


// add_callback
// ------------

function void ovm_event::add_callback (ovm_event_callback cb,
                                       bit append=1);
  for (int i=0;i<callbacks.size();i++) begin
    if (cb == callbacks[i]) begin
      ovm_report_warning("CBRGED","add_callback: Callback already registered. Ignoring.");
      return;
    end
  end
  if (append)
    callbacks.push_back(cb);
  else
    callbacks.push_front(cb);
endfunction


// delete_callback
// ---------------

function void ovm_event::delete_callback (ovm_event_callback cb);
  for (int i=0;i<callbacks.size();i++) begin
    if (cb == callbacks[i]) begin
      callbacks.delete(i);
      return;
    end
  end
  ovm_report_warning("CBNTFD", "delete_callback: Callback not found. Ignoring delete request.");
endfunction

function void ovm_event::do_print (ovm_printer printer);
  printer.print_field("num_waiters", num_waiters, $bits(num_waiters), OVM_DEC, ".", "int");
  printer.print_field("on", on, $bits(on), OVM_BIN, ".", "bit");
  printer.print_time("trigger_time", trigger_time);
  printer.print_object("trigger_data", trigger_data);
  printer.m_scope.down("callbacks", null);
  foreach(callbacks[e]) begin
    printer.print_object($psprintf("[%0d]",e), callbacks[e], "[");
  end
  printer.m_scope.up(null);
endfunction

function void ovm_event::do_copy (ovm_object rhs);
  ovm_event e;
  super.do_copy(rhs);
  if(!$cast(e, rhs) || (e==null)) return;

  m_event = e.m_event;
  num_waiters = e.num_waiters;
  on = e.on;
  trigger_time = e.trigger_time;
  trigger_data = e.trigger_data;
  for(int i=0; i<callbacks.size(); ++i) void'(callbacks.pop_front());
  for(int i=0; i<e.callbacks.size(); ++i) callbacks.push_back(e.callbacks[i]);
endfunction


//------------------------------------------------------------------------------
//
// CLASS: ovm_barrier
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_barrier::new (string name="",
                           int threshold=0);
  ovm_event e;
  super.new(name);
  e = new({"barrier_",name});
  this.threshold = threshold;
  this.m_event = e;
  this.num_waiters = 0;
  this.auto_reset = 1;
  this.at_threshold = 0;
endfunction


// get_type_name
// -------------

function string ovm_barrier::get_type_name ();
  return type_name;
endfunction


// create
// ------

function ovm_object ovm_barrier::create (string name=""); 
  ovm_barrier v;
  v=new(name);
  return v;
endfunction


// wait_for
// --------

task ovm_barrier::wait_for ();
  if (this.at_threshold)
    return;

  this.num_waiters++;

  if (reached_threshold()) begin
    if (!this.auto_reset)
      this.at_threshold=1;
    this.m_trigger();
    return;
  end

  this.m_event.wait_trigger();
endtask
 

// m_trigger (private)
// ---------

task ovm_barrier::m_trigger ();

  this.m_event.trigger();
  this.num_waiters=0;
  #0; //this process was last to wait; allow other procs to resume first

endtask


// reset
// -----

function void ovm_barrier::reset (bit wakeup=1);
  this.at_threshold = 0;
  if (this.num_waiters) begin
    if (wakeup)
      this.m_event.trigger();
    else
      this.m_event.reset();
  end
  this.num_waiters = 0;
endfunction


// cancel
// ------

function void ovm_barrier::cancel ();
  this.m_event.cancel();
  this.num_waiters = this.m_event.get_num_waiters();
endfunction


// get_threshold
// -------------

function int ovm_barrier::get_threshold ();
  return this.threshold;
endfunction


// set_threshold
// ------------

function void ovm_barrier::set_threshold (int threshold);
  this.threshold = threshold;
  if (threshold <= num_waiters)
    this.reset(1);
endfunction


// set_auto_reset
// --------------

function void ovm_barrier::set_auto_reset (bit value=1);
  this.at_threshold = 0;
  this.auto_reset = value;
endfunction


// reached_threshold
// -----------------

function bit ovm_barrier::reached_threshold ();
  return (this.num_waiters >= this.threshold);
endfunction


// get_num_waiters
// ---------------

function int ovm_barrier::get_num_waiters ();
  return this.num_waiters;
endfunction

function void ovm_barrier::do_print (ovm_printer printer);
  printer.print_field("threshold", threshold, $bits(threshold), OVM_DEC, ".", "int");
  printer.print_field("num_waiters", num_waiters, $bits(num_waiters), OVM_DEC, ".", "int");
  printer.print_field("at_threshold", at_threshold, $bits(at_threshold), OVM_BIN, ".", "bit");
  printer.print_field("auto_reset", auto_reset, $bits(auto_reset), OVM_BIN, ".", "bit");
endfunction

function void ovm_barrier::do_copy (ovm_object rhs);
  ovm_barrier b;
  super.do_copy(rhs);
  if(!$cast(b, rhs) || (b==null)) return;

  threshold = b.threshold;
  num_waiters = b.num_waiters;
  at_threshold = b.at_threshold;
  auto_reset = b.auto_reset;
  m_event = b.m_event;

 endfunction  

//------------------------------------------------------------------------------
//
// CLASS: ovm_event_pool
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_event_pool::new (string name=""); 
  super.new(name);
endfunction


// get_type_name
// -------------

function string ovm_event_pool::get_type_name ();
  return type_name;
endfunction


// create
// ------

function ovm_object ovm_event_pool::create (string name=""); 
  ovm_event_pool v;
  v=new(name);
  return v;
endfunction


// get_global_pool (static)
// ---------------

function ovm_event_pool ovm_event_pool::get_global_pool ();
  if (m_global_pool==null) begin
    ovm_event_pool pool;
    pool = new("pool");
    m_global_pool = pool;
  end
  return m_global_pool;
endfunction


// get
// ---

function ovm_event ovm_event_pool::get (string name);
  ovm_event e;
  if(this.pool.exists(name)) e = this.pool[name];

  if (e==null) begin
     e = new (name);
     this.pool[name] = e;
  end
  return e;
endfunction


// num
// ---

function int ovm_event_pool::num ();
  return this.pool.num();
endfunction


// delete
// ------

function void ovm_event_pool::delete (string name);
  if (!this.exists(name)) begin
    ovm_report_warning("EVNTX", $psprintf("delete: %0s doesn't exist. Ignoring delete request",name));
    return;
  end
  this.pool.delete(name);
endfunction


// exists
// ------

function int ovm_event_pool::exists (string name);
  return this.pool.exists(name);
endfunction


// first
// -----

function int ovm_event_pool::first (ref string name);
  return this.pool.first(name);
endfunction


// last
// ----

function int ovm_event_pool::last (ref string name);
  return this.pool.last(name);
endfunction


// next
// ----

function int ovm_event_pool::next (ref string name);
  return this.pool.next(name);
endfunction


// prev
// ----

function int ovm_event_pool::prev (ref string name);
  return this.pool.prev(name);
endfunction

function void ovm_event_pool::do_print (ovm_printer printer);
  printer.print_generic("pool", "aa_object_string", pool.num(), "-");
  printer.m_scope.down("pool", null);
  foreach(pool[e]) begin
    printer.print_object(e, pool[e], "[");
  end
  printer.m_scope.up(null);

endfunction

function void ovm_event_pool::do_copy (ovm_object rhs);
  ovm_event_pool ep;
  string key;
  super.do_copy(rhs);

  if (rhs == null) return;
  assert($cast(ep, rhs));

  pool.delete();
  if(ep.pool.first(key))
    do pool[key] = ep.pool[key];
    while(ep.pool.next(key));

endfunction


//------------------------------------------------------------------------------
//
// CLASS: ovm_barrier_pool
//
//------------------------------------------------------------------------------

// new
// ---

function ovm_barrier_pool::new (string name=""); 
  super.new(name);
endfunction


// get_type_name
// -------------

function string ovm_barrier_pool::get_type_name ();
  return type_name;
endfunction


// create
// ------

function ovm_object ovm_barrier_pool::create (string name=""); 
  ovm_barrier_pool v;
  v=new(name);
  return v;
endfunction


// get_global_pool (static)
// ---------------

function ovm_barrier_pool ovm_barrier_pool::get_global_pool ();
  if (m_global_pool==null) begin
    ovm_barrier_pool pool;
    pool = new("pool");
    m_global_pool = pool;
  end
  return m_global_pool;
endfunction


// get
// ---

function ovm_barrier ovm_barrier_pool::get (string name);
  ovm_barrier b;
  if(this.pool.exists(name)) b = this.pool[name];
  if (b==null) begin
     b = new (name);
     this.pool[name] = b;
  end
  return b;
endfunction


// num
// ---

function int ovm_barrier_pool::num ();
  return this.pool.num();
endfunction


// delete
// ------

function void ovm_barrier_pool::delete (string name);
  if (!this.exists(name)) begin
    ovm_report_warning("BRNTEX", $psprintf("delete: %0s doesn't exist. Ignoring delete request",name));
    return;
  end
  this.pool.delete(name);
endfunction


// exists
// ------

function int ovm_barrier_pool::exists (string name);
  return this.pool.exists(name);
endfunction


// first
// -----

function int ovm_barrier_pool::first (ref string name);
  return this.pool.first(name);
endfunction


// last
// ----

function int ovm_barrier_pool::last (ref string name);
  return this.pool.last(name);
endfunction


// next
// ----

function int ovm_barrier_pool::next (ref string name);
  return this.pool.next(name);
endfunction


// prev
// ----

function int ovm_barrier_pool::prev (ref string name);
  return this.pool.prev(name);
endfunction

function void ovm_barrier_pool::do_print (ovm_printer printer);
  printer.print_generic("pool", "aa_object_string", pool.num(), "-");
  printer.m_scope.down("pool", null);
  foreach(pool[e]) begin
    printer.print_object(e, pool[e], "[");
  end
  printer.m_scope.up(null);

endfunction

function void ovm_barrier_pool::do_copy (ovm_object rhs);
  ovm_barrier_pool bp;
  string key;
  super.do_copy(rhs);
  if(!$cast(bp, rhs) || (bp==null)) return;

  pool.delete();
  if(bp.pool.first(key))
    do pool[key] = bp.pool[key];
    while(bp.pool.next(key));

endfunction
