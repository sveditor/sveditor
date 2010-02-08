// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_report_global.svh#8 $
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

`ifndef OVM_REPORT_GLOBAL_SVH
`define OVM_REPORT_GLOBAL_SVH

// Function: ovm_report_enabled (global)
//
// Returns 1 if the report will be issued given the report's declared
// verbosity level and the configured verbosity level in ovm_top. The
// ovm_report_object also has an ovm_report_enabled method, which checks
// the report's declared verbosity level with the configured verbosity
// level for that particular instance (i.e., for the component instance.)
//
// Static methods of an extension of ovm_report_object can not call 
// ovm_report_enabled() because the call will resolve to the ovm_report_object
// non-static method. Static methods can not call non-static methods of the
// same class. 

function bit ovm_report_enabled (int verbosity);
  return (ovm_top.get_report_verbosity_level() >= verbosity);
endfunction


// Functions: ovm_report_<severity>
//
// Provides a set of global reporting functions, which delegate to
// the ovm_top instance. These functions can be called from modules or
// any class not derived from ovm_report_object.

function void ovm_report_info(string id,
			      string message,
                              int verbosity = OVM_MEDIUM,
			      string filename = "",
			      int line = 0);
  ovm_top.ovm_report_info(id, message, verbosity, filename, line);
endfunction

function void ovm_report_warning(string id,
                                 string message,
                                 int verbosity = OVM_MEDIUM,
				 string filename = "",
				 int line = 0);
  ovm_top.ovm_report_warning(id, message, verbosity, filename, line);
endfunction

function void ovm_report_error(string id,
                               string message,
                               int verbosity = OVM_LOW,
			       string filename = "",
			       int line = 0);
  ovm_top.ovm_report_error(id, message, verbosity, filename, line);
endfunction

function void ovm_report_fatal(string id,
	                       string message,
                               int verbosity = OVM_NONE,
			       string filename = "",
			       int line = 0);
  ovm_top.ovm_report_fatal(id, message, verbosity, filename, line);
endfunction


`endif // OVM_REPORT_GLOBAL_SVH
