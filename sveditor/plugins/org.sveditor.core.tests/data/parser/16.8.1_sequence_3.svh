
module m;

	sequence event_arg_example (event ev);
	@(ev) x ##1 y;
	endsequence
	
	cover property (event_arg_example(posedge clk));
	
	cover property (@(posedge clk) x ##1 y);
endmodule