// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 

`ifndef RVM_RAL_VERSION__SV
`define RVM_RAL_VERSION__SV


class vmm_ral_version;
   extern function int major();
   extern function int minor();
   extern function int patch();
   extern function string vendor();
   extern function void display(string prefix = "");
   extern function string psdisplay(string prefix = "");
endclass: vmm_ral_version

function int vmm_ral_version::major();
   major = 1;
endfunction: major

function int vmm_ral_version::minor();
   minor = 13;
endfunction: minor

function int vmm_ral_version::patch();
   patch = 0;
endfunction: patch


function string vmm_ral_version::vendor();
   vendor = "Synopsys";
endfunction: vendor

function void vmm_ral_version::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

function string vmm_ral_version::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sVMM RAL Version %0d.%0d.%0d (%s)",
            prefix, this.major(), this.minor(), this.patch(),this.vendor());
endfunction: psdisplay

`endif // RVM_RAL_VERSION__SV
