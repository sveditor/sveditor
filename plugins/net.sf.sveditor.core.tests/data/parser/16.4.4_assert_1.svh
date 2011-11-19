
module m;
	always @(bad_val or bad_val_ok) begin : b1
		a1: assert #0 (bad_val) else $fatal("Sorry");
		if (bad_val_ok) begin
			disable a1;
		end
	end	
endmodule
