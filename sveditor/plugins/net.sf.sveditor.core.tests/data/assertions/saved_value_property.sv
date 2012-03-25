
module saved_value_property;

	property p1;
		bit [31:0] prev_val;
		@(posedge clk) ((a && val > 128), prev_val = num) |=> num == prev_val;
	endproperty

endmodule