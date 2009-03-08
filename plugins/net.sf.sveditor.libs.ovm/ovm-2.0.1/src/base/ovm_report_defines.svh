// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_report_defines.svh#12 $
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

`ifndef OVM_REPORT_DEFINES_SVH
`define OVM_REPORT_DEFINES_SVH

// enum severity
// a report is either a message, warning, error or fatal
typedef bit [1:0] ovm_severity;


typedef enum ovm_severity
{
  OVM_INFO,
  OVM_WARNING,
  OVM_ERROR,
  OVM_FATAL
} ovm_severity_type;

// an action is a 4 bit integer built by bitwise or'ing of
// the following actions : DISPLAY, LOG, COUNT, and EXIT
// 
// DISPLAY sends the report to the standard output
// LOG sends the report to the file(s) for this (severity,id) pair
// COUNT counts the number of reports with the COUNT attribute.
// When this value reaches max_quit_count, the simulation terminates
// EXIT terminates the simulation immediately.

`ifndef IUS_SVPP_LIMIT
typedef bit [5:0] ovm_action;

typedef enum ovm_action
{
  OVM_NO_ACTION = 6'b000000,
  OVM_DISPLAY   = 6'b000001,
  OVM_LOG       = 6'b000010,
  OVM_COUNT     = 6'b000100,
  OVM_EXIT      = 6'b001000,
  OVM_CALL_HOOK = 6'b010000,
  OVM_STOP      = 6'b100000
} ovm_action_type;
`else
typedef int ovm_action;

typedef enum
{
  OVM_NO_ACTION = 'b000000,
  OVM_DISPLAY   = 'b000001,
  OVM_LOG       = 'b000010,
  OVM_COUNT     = 'b000100,
  OVM_EXIT      = 'b001000,
  OVM_CALL_HOOK = 'b010000,
  OVM_STOP      = 'b100000
} ovm_action_type;
`endif

// Verbosity values are just integers. This enum provides some predefind verbosity
// levels.

typedef enum {
  OVM_NONE   = 0,
  OVM_LOW    = 100,
  OVM_MEDIUM = 200,
  OVM_HIGH   = 300,
  OVM_FULL   = 400,
  OVM_DEBUG  = 500
} ovm_verbosity;

typedef int OVM_FILE;
typedef ovm_action id_actions_array[string];
typedef OVM_FILE id_file_array[string];

ovm_action s_default_action_array[string]; // default is already NO_ACTION
OVM_FILE s_default_file_array[string]; // default is already 0

`endif // OVM_REPORT_DEFINES_SVH
