
module t;
	clocking dram @(clk);
		input #1ps address;
		input #5 output #6 data;
	endclocking

endmodule
