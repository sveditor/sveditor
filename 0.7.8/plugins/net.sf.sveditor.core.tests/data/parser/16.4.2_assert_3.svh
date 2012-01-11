
module m;
	assign a = 1;
	assign b = 2;
	always_comb begin : b1
		c1: cover (b != a);
		c2: cover #0 (b != a);
	end	
endmodule
