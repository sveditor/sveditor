
module m;
	// ??
	
	global clocking @clk; endclocking
	// ...
	assert property(@$global_clock a);
	
	base_rule1: assert property (cont_prop(rst,in1,in2)) $display("%m, passing");
		else $display("%m, failed");	
	
	
endmodule
