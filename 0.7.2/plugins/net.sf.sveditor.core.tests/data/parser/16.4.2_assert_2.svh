
module m;
	always @(a or b) begin : b1
		a3: assert #0 (a == b) rptobj.success(0); else rptobj.error(0, a, b);
		#1;
		a4: assert #0 (a == b) rptobj.success(1); else rptobj.error(1, a, b);
	end

endmodule
