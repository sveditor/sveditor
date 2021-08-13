
module m;
	
	assert property ( @(posedge clk)
		disable iff (a && $rose(b, @(posedge clk))) trigger |=> test_expr );
	
endmodule
