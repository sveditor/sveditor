// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_agent.svh#4 $
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

`ifndef OVM_AGENT_SVH
`define OVM_AGENT_SVH

//------------------------------------------------------------------------------
//
// CLASS: ovm_agent
//
// declaration - base for all uVC agents.
//------------------------------------------------------------------------------

virtual class ovm_agent extends ovm_component;

  // Constructor
  extern function new (string name, ovm_component parent);

  task run; begin end endtask

endclass

`endif // OVM_AGENT_SVH

