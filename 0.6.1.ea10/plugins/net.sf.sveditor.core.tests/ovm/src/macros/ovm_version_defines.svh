//----------------------------------------------------------------------
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
//----------------------------------------------------------------------

`ifndef OVM_VERSION_DEFINES_SVH
`define OVM_VERSION_DEFINES_SVH

// Version numbers to be used in creating version strings for printing
// or programmatic tesing against version numbers
`define OVM_NAME OVM
`define OVM_MAJOR_REV 2
`define OVM_MINOR_REV 0
`define OVM_FIX_REV 3


// Whole version identifiers that can be used in `ifdefs and `ifndefs
// to do conditional compilation
`define OVM_VERSION_2_0_3
`define OVM_MAJOR_VERSION_2_0
`define OVM_MAJOR_REV_2
`define OVM_MINOR_REV_0
`define OVM_FIX_REV_3

`define OVM_VERSION_STRING `"`OVM_NAME``-```OVM_MAJOR_REV``.```OVM_MINOR_REV``.```OVM_FIX_REV`"

`endif // OVM_VERSION_DEFINES_SVH
