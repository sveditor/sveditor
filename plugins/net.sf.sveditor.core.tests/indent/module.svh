
`timescale 1ns/1ps

module top(
		input			clk,
		output			dat);
	
	function void foobar();
		int a;
		a = 5;
	endfunction

	always @(posedge clk)
		dat = 1;

	always @(posedge clk) begin
		dat = 1;
		dat = 2;
	end

endmodule
