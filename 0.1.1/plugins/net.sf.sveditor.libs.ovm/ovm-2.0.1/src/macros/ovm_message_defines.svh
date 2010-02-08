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

`ifndef OVM_MESSAGE_DEFINES_SVH
`define OVM_MESSAGE_DEFINES_SVH

`ifndef OVM_LINE_WIDTH
  `define OVM_LINE_WIDTH 120
`endif 

`ifndef OVM_NUM_LINES
  `define OVM_NUM_LINES 120
`endif

// When both simulators support them, the `__FILE and `__LINE macros
// will replace all occurrences of `ovm_file and `ovm_line.

`ifndef INCA
  `define SV_FILE_LINE
`endif
 
`ifndef SV_FILE_LINE
`define ovm_file "<UNKNOWN>"
`define ovm_line 0
`else
`define ovm_file `__FILE__
`define ovm_line `__LINE__
`endif

`define OVM_REPORT_INFO(ID,MSG) \
  ovm_report_info(ID,MSG,OVM_MEDIUM,`ovm_file,`ovm_line)

`define OVM_REPORT_WARNING(ID,MSG) \
  ovm_report_warning(ID,MSG,OVM_MEDIUM,`ovm_file,`ovm_line)

`define OVM_REPORT_ERROR(ID,MSG) \
  ovm_report_error(ID,MSG,OVM_LOW,`ovm_file,`ovm_line)

`define OVM_REPORT_FATAL(ID,MSG) \
  ovm_report_fatal(ID,MSG,OVM_NONE,`ovm_file,`ovm_line)


`endif // OVM_MESSAGE_DEFINES_SVH
