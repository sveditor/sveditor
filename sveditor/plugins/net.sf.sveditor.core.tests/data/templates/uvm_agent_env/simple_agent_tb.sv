
`include "uvm_macros.svh"
module simple_agent_tb;
	import uvm_pkg::*;
	import simple_agent_pkg::*;

	`include "simple_agent_test_seq_item.svh"	
	`include "simple_agent_test_seq.svh"	
	`include "simple_agent_test_subscriber.svh"	
	`include "simple_agent_test.svh"
	
	initial begin
		run_test("simple_agent_test");
	end

endmodule
