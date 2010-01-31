// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_test.svh#5 $
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

`ifndef OVM_TEST_SVH
`define OVM_TEST_SVH


//------------------------------------------------------------------------------
//
// CLASS: ovm_test
//
// Declaration of the base class for all user tests.
//------------------------------------------------------------------------------

virtual class ovm_test extends ovm_component;
  
  // Constructor
  extern function new(string name, ovm_component parent);

  // Need to implement for ovm_threaded component. Tests don't require a run
  // phase, but may have one.
  extern task run;
endclass


`endif // OVM_TEST_SVH
