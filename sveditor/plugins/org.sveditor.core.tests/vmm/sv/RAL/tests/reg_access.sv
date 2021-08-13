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


`ifndef VMM_RAL_TEST_PRE_INCLUDE
`define VMM_RAL_TEST_PRE_INCLUDE ral_env.svh
`endif

`include "vmm.sv"

`include `VMM_MACRO_TO_STRING(`VMM_RAL_TEST_PRE_INCLUDE)

program reg_access;

`ifdef VMM_RAL_TEST_POST_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_RAL_TEST_POST_INCLUDE)
`endif

`ifndef RAL_TB_ENV
`define RAL_TB_ENV tb_env
`endif


vmm_log log = new("Register Access", "Test");
`RAL_TB_ENV env;

vmm_ral_tests _vmm_ral_tests = new;

initial
begin
   vmm_ral_block_or_sys ral_model;
   vmm_ral_block blk;
   vmm_ral_block blks[];
   string        domains[];

   env = new;

   ral_model = env.ral.get_model();
   if (ral_model == null) begin
      `vmm_fatal(log, "No RAL abstraction model was specified");
   end

   env.reset_dut();
   ral_model.reset();

   // Test each block in turn

   if ($cast(blk, ral_model)) begin
      // Blocks with some attributes are not to be tested
      if (blk.get_attribute("NO_RAL_TESTS") == "" &&
          blk.get_attribute("NO_REG_ACCESS_TEST") == "") begin

         _vmm_ral_tests.reg_access(blk, log);
      end
   end
   else begin
      int blks_size;
      vmm_ral_sys sys;
      $cast(sys, ral_model);
      sys.get_all_blocks(blks, domains);

      // Uniquify the blocks (the same block could be in >1 domains)
      blks_size = blks.size();
      foreach (blks[i]) begin
         if (i < blks_size-1) begin
            for (int j = i + 1; j < blks_size; j++) begin
               if (blks[i] == blks[j]) blks[j] = null;
            end
         end
      end

      foreach (blks[i]) begin
         if (blks[i] == null) continue;

         // Blocks with some attributes are not to be tested
         if (blks[i].get_attribute("NO_RAL_TESTS") != "" ||
             blks[i].get_attribute("NO_REG_ACCESS_TEST") != "") continue;
         
         _vmm_ral_tests.reg_access(blks[i], log);
      end
   end
   
   log.report();
end
endprogram: reg_access
