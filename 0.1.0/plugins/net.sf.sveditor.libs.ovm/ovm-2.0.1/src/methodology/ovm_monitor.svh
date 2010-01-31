// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_monitor.svh#3 $
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

`ifndef OVM_MONITOR_SVH
`define OVM_MONITOR_SVH

//-----------------------------------------------------------------------------
//
// CLASS: ovm_monitor
//
// declaration - the base-class for all derived monitors.
//-----------------------------------------------------------------------------

virtual class ovm_monitor extends ovm_component;

  // Constructor
  extern function new (string name, ovm_component parent);
  
endclass

`endif // OVM_MONITOR_SVH

