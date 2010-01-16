// $Id: //dvt/vtech/dev/main/ovm/src/base/base.svh#14 $
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

`ifndef OVM_BASE_SVH
`define OVM_BASE_SVH

  `const string s_deprecated_3_0 = "Deprecated in AVM 3.0 and later";

  // Miscellaneous classes and functions. ovm_void is defined in ovm_misc,
  // along with some auxillary functions that OVM needs but are not really
  // part of OVM.
  `include "base/ovm_version.svh"
  `include "base/ovm_misc.sv"
  `include "base/ovm_report_defines.svh"

  // The base object element. Contains data methods (copy/compare etc) and
  // factory creation methods (create). Also includes control classes.
  `include "base/ovm_object.sv"
  `include "base/ovm_printer.sv"
  `include "base/ovm_packer.sv"

  // Event interface
  `include "base/ovm_event.sv"

  // Reporting interface
  `include "base/ovm_report_server.svh"
  `include "base/ovm_report_handler.svh"
  `include "base/ovm_report_object.svh"
  `include "base/ovm_report_global.svh"

  // Base transaction object
  `include "base/ovm_transaction.sv"

  // The phase declarations. ovm_component does the actual phasing.
  `include "base/ovm_phases.sv"

  // ovm_component has a co-dependency with the factory. 
  `include "base/ovm_factory.sv"
  `include "base/ovm_config.svh"

  `include "base/ovm_component.sv"
  `include "base/ovm_env.svh"
  `include "base/ovm_registry.svh"

  `include "base/ovm_extern_report_server.svh"

  // for urm message compatibility. Must be included otherwise ovm_component will not compile
  `include "compatibility/urm_message.sv"

`endif // OVM_BASE_SVH
