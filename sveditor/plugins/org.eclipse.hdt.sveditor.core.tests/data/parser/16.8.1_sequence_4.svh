
module m;
	
	sequence event_arg_example2 (reg sig);
	@(posedge sig) x ##1 y;
	endsequence
	cover property (event_arg_example2(clk));	
	
	cover property (@(posedge clk) x ##1 y);
	
endmodule