
module m;
	property p3;
		b ##1 c;
	endproperty
	
	c1: cover property (@(posedge clk) a #-# p3);
	a1: assert property (@(posedge clk) a |-> p3);	
endmodule