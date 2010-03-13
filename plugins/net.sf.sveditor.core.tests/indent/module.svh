
`timescale 1ns/1ps

module top(
		input			clk,
		output			dat);

	function void foobar();
		int a;
		a = 5;
	endfunction

endmodule
