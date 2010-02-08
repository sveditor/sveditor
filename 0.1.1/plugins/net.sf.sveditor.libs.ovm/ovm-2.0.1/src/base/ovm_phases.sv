// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_phases.sv#20 $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

`ifndef OVM_PHASES_SVH
`define OVM_PHASES_SVH

typedef class ovm_component;

//------------------------------------------------------------------------------
//
// Class: ovm_phase
//
//------------------------------------------------------------------------------
// This class is a base class for a phase callback. All predefined OVM phases
// and any user-defined phases alike use ovm_phase. To define a new phase:
//
// (1)  derive a subclass of ovm_phase that implements (overrides) either the
//      call_task  or call_func method, depending on whether the new phase is
//      to be time-consuming or not.  When calling super.new, your subclass must
//      provide the name of phase (typically the name of the callback method),
//      whether the method is to be called top-down or bottom-up, and whether
//      the method is task or a function. For example, given a component type,
//      my_comp, you can define a my_task phase for that component as follows:
//
//        class my_comp extends ovm_component;
//          ...
//          virtual my_task();  return; endtask // make virtual
//          ...
//        endclass
//
//        class my_task_phase extends ovm_phase;
//          function new();
//            super.new("my_task",1,1);
//          endfunction
//          task call_task(ovm_component parent);
//             my_comp_type my_comp;
//             if ($cast(my_comp,parent))
//               my_comp.my_task_phase()
//          endtask
//        endclass
//      
//      Tip: The above can be defined via a convenient macro invocation:
//
//           `ovm_phase_task_topdown_decl(my_task)
//
// (2)  Create a global (or package-scope) instance of your phase object:
//
//        my_task_phase my_task_ph = new();
//
// (3)  Register the phase with the OVM's phase controller, ovm_top. For
//      example, to register the my_task_phase as a phase for all my_comp-
//      based components:
//        
//        ovm_top.insert_phase(my_task_ph, run_ph);
//
//      It should be global in nature so that it is universally available 
//      to any process for getting or waiting on phase state.
//
// That's it! The ovm_top phase controller will now call my_comp-based components'
// my_task phase callbacks in top-down order after completion of the run phase.
//
//
// Type information methods:
//
//   The methods get_name, is_task, and is_top_down provide information about
//   the phase's type.
// 
// Event & status methods:
//
//   The ovm_phase class defines an event interface that allows processes to
//   wait until the phase begins or ends and to determine whether the phase is
//   currently active (is_in_progress) or has completed (is_done). The reset
//   method clears the phase state.
//
//------------------------------------------------------------------------------


virtual class ovm_phase;

  local  string  m_name;
  local  bit     m_is_top_down;
  local  bit     m_is_task;

  local  event   m_start_event;
  local  bit     m_is_started=0;
  local  event   m_done_event;
  local  bit     m_is_done=0;
  local  bit     m_executed[int];

  local  ovm_phase m_aliases[$];
  local  ovm_phase m_insertion_phase;

  function new (string name, bit is_top_down, bit is_task);
    m_name = name;
    m_is_top_down = is_top_down;
    m_is_task     = is_task;
  endfunction

  //
  // Info interface
  //
  function string get_name       (); return m_name;        endfunction
  function bit    is_task        (); return m_is_task;     endfunction
  function bit    is_top_down    (); return m_is_top_down; endfunction

  virtual function string get_type_name();
    return "ovm_phase";
  endfunction

  //
  // Event & Status interface
  //
  task            wait_start     (); @m_start_event;       endtask
  task            wait_done      (); @m_done_event;        endtask

  function bit    is_in_progress (); return m_is_started;  endfunction
  function bit    is_done        (); return m_is_done;     endfunction

  function void   reset          (); m_is_done=0;
                                     m_is_started=0;       
                                     m_executed.delete();
                                     foreach(m_aliases[i]) 
                                       m_aliases[i].reset(); endfunction

  //
  // Virtual methods call_task/call_func: subclasses must define only one
  //
  virtual task call_task (ovm_component parent);
     foreach(m_aliases[i]) m_aliases[i].call_task(parent);
     return;
  endtask

  virtual function void call_func (ovm_component parent);
     foreach(m_aliases[i]) m_aliases[i].call_func(parent);
    return;
  endfunction

  // psuedo-private methods; do not call directly

  function void m_set_is_started(bit val);
    foreach(m_aliases[i]) m_aliases[i].m_set_is_started(val);
    m_is_started=val;
  endfunction

  function void m_set_in_progress();
    foreach(m_aliases[i]) m_aliases[i].m_set_in_progress();
    m_set_is_started(1);
    ->m_start_event;
  endfunction

  function void m_set_done();
    foreach(m_aliases[i]) m_aliases[i].m_set_done();
    m_is_done=1;
    m_set_is_started(0);
    ->m_done_event;
  endfunction

  function void set_insertion_phase(ovm_phase phase);
    if(m_insertion_phase != null) begin
      ovm_report_warning("INSPHS", "Cannot set the insertion phase for a phase that has already been set");
      return;
    end
    m_insertion_phase = phase;
  endfunction

  function ovm_phase get_insertion_phase();
    return m_insertion_phase;
  endfunction

  function bit has_executed(ovm_component comp);
    if(m_executed.exists(comp.get_inst_id())) return 1;
    foreach(m_aliases[i])
      if(m_aliases[i].has_executed(comp)) return 1;
    return 0;
  endfunction

  function void set_executed(ovm_component comp);
    m_executed[comp.get_inst_id()] = 1;
  endfunction

  function void add_alias(ovm_phase the_alias, exist_ph);
    ovm_phase insertion_phase;
    string    alias_nm, insrt_nm, alias_insrt_nm;
    //if the alias is null then return
    if(the_alias == null) return;
    if(the_alias == this && m_insertion_phase == exist_ph) return;

    alias_nm = the_alias.get_name();

    //This warning can't happen from ovm_root, but in theory a user could create
    //their own phase controller in which case, aliasing different names is probably
    //not desireable.
    if(alias_nm != get_name()) begin
      ovm_report_warning("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, but have different phase names"});
    end

    //verify that the aliased phase has the same semantics as the
    //master phase.
    if(m_is_task != the_alias.is_task()) begin
      ovm_report_fatal("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, but one is a function phase and one is a task phase"});
      return;
    end
    if(m_is_top_down != the_alias.is_top_down()) begin
      ovm_report_fatal("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, but one is top-down and the other is bottom-up"});
      return;
    end
    if(exist_ph != null)
       alias_insrt_nm = exist_ph.get_name();
    else
       alias_insrt_nm = "the topmost phase";
    if(m_insertion_phase != null)
       insrt_nm = m_insertion_phase.get_name();
    else
       insrt_nm = "the topmost phase";
    if(insrt_nm != alias_insrt_nm) begin
      ovm_report_fatal("PHSALS", {
        "Phases ", get_name(), " and ", alias_nm, 
        " are being aliased, they have different insertion phase, \"",
        insrt_nm, "\" versus \"", alias_insrt_nm, "\""}); 
      return;
    end

    //for existing aliases, we needed to verify the insertion phase
    //which is why we wait to the end before we exit.
    foreach(m_aliases[i]) if (the_alias == m_aliases[i]) return;
    if(the_alias == this) return;

    the_alias.set_insertion_phase(exist_ph);
    m_aliases.push_back(the_alias);
  endfunction
endclass


`endif // OVM_PHASES_SVH
