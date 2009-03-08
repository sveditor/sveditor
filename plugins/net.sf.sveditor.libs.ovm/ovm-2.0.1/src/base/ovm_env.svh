// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_env.svh#20 $
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

//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//
// CLASS: ovm_env
//
//------------------------------------------------------------------------------
// The ovm_env component is intended to be a container of components that
// together comprise a complete environment. The environment may
// initially consist of the entire testbench. Later, it can be reused as
// a child-env of even larger system-level environments.
//
// AVM compatibility (do_test) mode: (deprecated, do not use in new code)
//
//   The top-most ovm_env's run phase has special semantics when
//   simulation is started via 'do_test', i.e. AVM backward compatibility
//   mode. When the top env's run task returns, an automatic global_stop_
//   request is issued, thus ending the run phase. When not in 'do_test'
//   mode, the run phase behaves like any other- when it returns, it does
//   signify the end of the phase. Rather, an explicit global_stop_request
//   must be issued to end the phase. 
//------------------------------------------------------------------------------

virtual class ovm_env extends ovm_component;

  function new (string name="env", ovm_component parent=null);
    super.new(name,parent);
  endfunction

  const static string type_name = "ovm_env";

  virtual function string get_type_name ();
    return type_name;
  endfunction

  bit m_do_test_mode = 0;

  task do_task_phase (ovm_phase phase);
  
    // Top-level env has special run-phase semantic when in 'do_test' mode.
    // In all other cases, ovm_env's run phase behaves like any other.

    m_curr_phase = phase;

    if (!(m_do_test_mode && phase == run_ph && m_parent == ovm_top)) begin
      super.do_task_phase(phase);
      return;
    end

    // Delay 1 delta to ensure this env's process starts last, thus
    // allowing sub-tree of components to initialize before this
    // run-task starts.

    #0;

    // QUESTA
    `ifndef INCA  

       m_phase_process = process::self();
       phase.call_task(this);

    // INCISIVE
    `else

       // isolate inner process so it can be safely killed via disable fork,
       fork
       begin
         fork : task_phase
           phase.call_task(this);
           @m_kill_request;
         join_any
         disable task_phase;
       end
       join

    `endif

    ovm_top.stop_request(); // ends run phase

  endtask

  task do_test();
   ovm_report_warning("deprecated", {"do_test mode is deprecated. Use ",
                     "run_test to start simulation phasing, and be ",
                     "sure to call global_stop_request() to end the ",
                     "run phase and any other task-based phase."});
    m_do_test_mode=1;
    ovm_top.run_global_phase();
    report_summarize();
  endtask

  task run_test(string name="");
    ovm_top.run_test(name);
  endtask

endclass


