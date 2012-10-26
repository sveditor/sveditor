
module t;
	clocking cd1 @(posedge phi1);
		input #1step state = top.cpu.state;
	endclocking
	
	clocking mem @(clock);
		input instruction = {opcode, regA, regB[3:1]};
	endclocking

endmodule