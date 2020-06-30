
module t;
	clocking ck1 @(posedge clk);
		default input #1step output negedge; 
		// outputs driven on the negedge clk
	endclocking
	
	clocking ck2 @(clk); // no edge specified
		default input #1step output negedge;
	endclocking
	
	clocking bus @(posedge clock1);
		default input #10ns output #2ns;
		input data, ready, enable = top.mem1.enable;
		output negedge ack;
		input #1step addr;
	endclocking

endmodule
