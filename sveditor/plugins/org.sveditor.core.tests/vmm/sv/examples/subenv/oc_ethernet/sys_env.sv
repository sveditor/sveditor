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


`include "vmm_ral.sv"

`include "wishbone.sv"
`include "mii.sv"

`include "ral_dual_eth.sv"
`include "eth_subenv.sv"

class test_cfg;
   rand oc_eth_subenv_cfg eth[2];

   rand wb_slave_cfg  ram;
   rand vmm_mam_cfg   mam;

   constraint test_cfg_valid {
      ram.port_size   == wb_cfg::DWORD;
      ram.granularity == wb_cfg::BYTE; 
      ram.cycles      == wb_cfg::CLASSIC;
      ram.min_addr    == 32'h0000_0000;
      ram.max_addr    == 32'hFFFF_FFFF;

      mam.n_bytes      == 4;
      mam.start_offset == ram.min_addr;
      mam.end_offset   == ram.max_addr;
   }

   function new();
      foreach (this.eth[i]) begin
         this.eth[i] = new;
      end
      this.ram = new;
      this.mam = new;
   endfunction: new

   function string psdisplay(string prefix = "");
      psdisplay = {this.eth[0].psdisplay(prefix), "\n",
                   this.eth[1].psdisplay(prefix)};
      $sformat(psdisplay, "%s\n%s", psdisplay, this.ram.psdisplay(prefix));
   endfunction
endclass: test_cfg


class wb_cycle_resp_no_wss extends wb_cycle_resp;
   function new(wb_cycle     req,
                wb_slave_cfg cfg);
      super.new(req, cfg);
   endfunction

   constraint no_wss {
      n_wss == 0;
   }

   function vmm_data copy(vmm_data to);
      wb_cycle_resp_no_wss tr;

      if (to == null) tr = new(null, null);
      else if (!$cast(tr, to)) begin
         `vmm_fatal(this.log, "Unable to copy to non-wb_cycle_resp_no_wss instance");
         return null;
      end

      return super.copy(tr);
   endfunction: copy

endclass


class ral_to_wb extends vmm_rw_xactor;
   wb_master bfm;
   wb_cfg    cfg;

   function new(string        inst,
                int unsigned  stream_id,
                wb_master     bfm,
                wb_cfg        cfg);
      super.new("WishBone RAL Master", inst, stream_id);

      this.bfm = bfm;
      this.cfg = cfg;
   endfunction: new

   virtual function void start_xactor();
      super.start_xactor();
      this.bfm.start_xactor();
   endfunction

   virtual function void stop_xactor();
      super.stop_xactor();
      this.bfm.stop_xactor();
   endfunction

   virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
      super.reset_xactor(rst_typ);
      this.bfm.reset_xactor(rst_typ);
   endfunction

   virtual task execute_single(vmm_rw_access tr);
      wb_cycle cyc;
      bit ok;
      
      cyc = new(this.cfg);

      if (tr.kind == vmm_rw::WRITE) begin
         ok = cyc.randomize() with {kind == wb_cycle::WRITE;
                                    // BYTE granularity in DWORD bus size
                                    addr == tr.addr << 2;
                                    data == tr.data;
                                    sel  == 4'hF;
                                    lock == 1'b0;};
      end
      else begin
         ok = cyc.randomize() with {kind == wb_cycle::READ;
                                    // BYTE granularity in DWORD bus size
                                    addr == tr.addr << 2;
                                    sel  == 4'hF;
                                    lock == 1'b0;};
      end
      if (!ok) begin
         `vmm_fatal(this.log, {"Unable to translate generic RW access into WB cycle:\n",
                               tr.psdisplay("   "), "\n",
                               this.cfg.psdisplay("   ")});
         tr.status = vmm_rw::ERROR;
         return;
      end

      this.bfm.exec_chan.put(cyc);

      if (tr.kind == vmm_rw::READ) begin
         tr.data = cyc.data;
      end
      tr.status = (cyc.status == wb_cycle::ACK) ? vmm_rw::IS_OK : vmm_rw::ERROR;
   endtask: execute_single
endclass: ral_to_wb


//
// DMA Regions must start on a DWORD boundary
//
class allocate_on_dword extends vmm_mam_allocator;
   constraint dword_aligned {
      start_offset[1:0] == 2'b00;
   }
endclass: allocate_on_dword


class sys_env extends vmm_ral_env;
   test_cfg cfg;

   oc_eth_subenv eth[2];

   ral_sys_dual_eth ral_model;

   wb_slave  slv;
   wb_ram    ram;
   vmm_mam   dma_mam;

   mii_phy_layer phy[2];

   wb_master host;
   ral_to_wb ral_xlate;

   eth_frame_atomic_gen src;

   function new();
      super.new();
      this.cfg = new;

      this.ral_model = new(0);
      this.ral.set_model(this.ral_model);
      
      $timeformat(-9, 0, "ns", 1);
   endfunction: new

   virtual function void gen_cfg();
      bit ok;
      super.gen_cfg();

      ok = this.cfg.randomize();
      if (!ok) begin
         `vmm_fatal(log, "Failed to randomize test configuration");
      end
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      `vmm_note(this.log, this.cfg.psdisplay());

      this.phy[0] = new("PHY #0", 0, this.cfg.eth[0].mii,
                        sys_top.mii_0.phy_layer);
      this.phy[1] = new("PHY #1", 1, this.cfg.eth[1].mii,
                        sys_top.mii_1.phy_layer);
      this.phy[0].tx_chan.sink();
      this.phy[1].tx_chan.sink();

      begin
         wb_cycle_resp_no_wss no_wss_resp = new(null, this.cfg.ram);
         this.ram  = new("RAM",  1, null, null, no_wss_resp);
      end
      this.slv  = new("Slave",  1, this.cfg.ram, sys_top.wb_ma,
                      this.ram.req_chan, this.ram.resp_chan);

      this.dma_mam = new("WB DMA", this.cfg.mam);
      begin
         allocate_on_dword alloc = new;
         this.dma_mam.default_alloc = alloc;
      end

      this.host = new("Host", 1, this.cfg.ram, sys_top.wb_sl);
      this.ral_xlate = new("RAL<->WB", 0, this.host, this.cfg.ram);
      this.ral.add_xactor(this.ral_xlate);

      this.src = new("SysLvl Src", 1);

      this.eth[0] = new("Eth0", this.cfg.eth[0], this.end_vote,
                        sys_top.mii_0.passive, null,
                        this.ral_model.eth[0], this.ram, this.dma_mam);

      this.eth[1] = new("Eth1", this.cfg.eth[1], this.end_vote,
                        sys_top.mii_1.passive, this.src.out_chan,
                        this.ral_model.eth[1], this.ram, this.dma_mam);

      this.log.disable_types(vmm_log::INTERNAL_TYP , "/./", "/./");
   endfunction: build


   virtual task hw_reset();
      sys_top.rst <= 1;
      repeat (3) @ (posedge sys_top.wb_clk);
      sys_top.rst <= 0;
   endtask: hw_reset

      
   virtual task cfg_dut();
      super.cfg_dut();
      fork
         this.eth[0].configure();
         this.eth[1].configure();
      join
      this.src.stop_after_n_insts = this.cfg.eth[1].run_for_n_frames;
   endtask: cfg_dut

   virtual task start();
      super.start();

      fork
         forever begin
            wait (sys_top.wb_int0);
            this.eth[0].frmwr.service_irq();
         end

         forever begin
            wait (sys_top.wb_int1);
            this.eth[1].frmwr.service_irq();
         end
      join_none

      this.src.start_xactor();
      this.phy[0].start_xactor();
      this.phy[1].start_xactor();
      this.slv.start_xactor();
      this.ram.start_xactor();
      this.eth[0].start();
      this.eth[1].start();

      this.end_vote.register_channel(this.host.exec_chan);
      this.end_vote.register_xactor(this.phy[0]);
      this.end_vote.register_xactor(this.phy[1]);
      this.end_vote.register_xactor(this.src);
      this.end_vote.register_xactor(this.host);

   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();

      // DMA must also have been idle for a while
      begin
         vmm_voter vote = this.end_vote.register_voter("DMA RAM");
         fork
            forever begin
               fork: wait_for_idle
                 begin
                    repeat (100) @ (posedge sys_top.wb_clk);
                    vote.consent("Is IDLE");
                 end
               join_none

               wait (sys_top.wb_sl.cyc);
               disable wait_for_idle;
               vote.oppose("Is BUSY");
               @ (negedge sys_top.wb_sl.cyc);
            end
         join_none
      end

      this.end_vote.wait_for_consensus();
   endtask: wait_for_end

   virtual task stop();
      super.stop();
      this.eth[0].stop();
      this.eth[1].stop();
   endtask: stop

   virtual task cleanup();
      super.cleanup();
      this.eth[0].cleanup();
      this.eth[1].cleanup();
   endtask: cleanup
endclass: sys_env
