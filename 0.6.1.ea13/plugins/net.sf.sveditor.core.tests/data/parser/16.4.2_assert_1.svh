
module m;
	assign not_a = !a;
	always_comb begin : b1
		a1: assert (not_a != a);
		a2: assert #0 (not_a != a); // Should pass once values have settled
	end
	
endmodule