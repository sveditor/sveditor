// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_version.svh#19 $
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

`ifndef OVM_VERSION_SVH
`define OVM_VERSION_SVH

parameter string ovm_name = "OVM";
parameter int    ovm_major_rev = 2;
parameter int    ovm_minor_rev = 0;
parameter int    ovm_fix_rev = 1;
parameter string ovm_mgc_copyright = "(C) 2007-2008 Mentor Graphics Corporation";
parameter string ovm_cdn_copyright = "(C) 2007-2008 Cadence Design Systems, Inc.";

function string ovm_revision_string();
  string s;
  if(ovm_fix_rev <= 0)
    $sformat(s, "%s-%1d.%1d", ovm_name, ovm_major_rev, ovm_minor_rev);
  else
    $sformat(s, "%s-%1d.%1d.%0d", ovm_name, ovm_major_rev, ovm_minor_rev, ovm_fix_rev);
  return s;
endfunction

`endif // OVM_VERSION_SVH
