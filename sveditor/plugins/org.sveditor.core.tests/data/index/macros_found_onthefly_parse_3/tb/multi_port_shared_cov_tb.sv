/****************************************************************************
 * multi_port_shared_cov_tb.sv
 ****************************************************************************/
`ifndef INCLUDED_multi_port_shared_cov_tb_sv
`define INCLUDED_multi_port_shared_cov_tb_sv

/**
 * Module: multi_port_shared_cov_tb
 * 
 * TODO: Add module documentation
 */
`include "uvm_macros.svh"
module multi_port_shared_cov_tb;
	import uvm_pkg::*;
	import multi_port_shared_cov_env_pkg::*;
	
	initial begin
		run_test();
	end


endmodule

`endif /* INCLUDED_multi_port_shared_cov_tb_sv */
