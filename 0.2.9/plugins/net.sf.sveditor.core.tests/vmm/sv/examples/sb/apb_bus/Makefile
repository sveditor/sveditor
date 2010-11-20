## 
## -------------------------------------------------------------
##    Copyright 2004-2008 Synopsys, Inc.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
## 

VMM	= $(VMM_HOME)/sv
APB	= apb

OPTS	=

#VCS	= vcs -R +plusarg_save -sverilog -ntb_opts dtm \
#              +incdir+$(APB)+$(VMM) +vmm_log_default=trace
VCS	= vlib work ; vlog -sv +define+VMM_NO_STR_DPI \
              +incdir+$(APB)+$(VMM) +vmm_log_default=trace 


all: simple

simple test_simple:
	$(VCS) $(OPTS) test_simple.sv tb_top.sv

clean:
	rm -rf csrc simv* vc_hdrs.h *~ apb/*~
