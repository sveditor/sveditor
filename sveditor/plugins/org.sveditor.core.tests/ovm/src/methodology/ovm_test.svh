// $Id: ovm_test.svh,v 1.8 2009/05/12 21:02:30 redelman Exp $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// CLASS: ovm_test
//
// This class is the virtual base class for the user-defined tests.
//
// The ovm_test virtual class should be used as the base class for user-defined
// tests. Doing so provides the ability to select which test to execute using
// the OVM_TESTNAME command line or argument to the <ovm_root::run_test> task.
//
// For example
//
//|  prompt> SIM_COMMAND +OVM_TESTNAME=test_bus_retry
//
// The global run_test() task should be specified inside an initial block
// such as
//
//|  initial run_test();
// 
// Multiple tests, identified by their type name, are compiled in and then
// selected for execution from the command line without need for recompilation.
// Random seed selection is also available on the command line.
//
// If +OVM_TESTNAME=test_name is specified, then an object of type 'test_name'
// is created by factory and phasing begins. Here, it is presumed that the
// test will instantiate the test environment, or the test environment will
// have already been instantiated before the call to run_test().
//
// If the specified test_name cannot be created by the <ovm_factory>, then a
// fatal error occurs. If run_test() is called without OVM_TESTNAME being
// specified, then all components constructed before the call to run_test will
// be cycled through their simulation phases.
//
// Deriving from ovm_test will allow you to distinguish tests from other
// component types that inherit from ovm_component directly. Such tests will
// automatically inherit features that may be added to ovm_test in the future.
//
//------------------------------------------------------------------------------

virtual class ovm_test extends ovm_component;
  
  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name,parent);
  endfunction
	
  const static string type_name = "ovm_test";

  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass

