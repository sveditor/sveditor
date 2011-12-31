
module m;
	always @(a or b or c) begin : b2
		if (c == 8'hff) begin	
			a2: assert #0 (a && b);
		end else begin
			a3: assert #0 (a || b);
		end
	end
	
	always @(clear_b2) begin : b3
		disable b2;
	end	
	
endmodule