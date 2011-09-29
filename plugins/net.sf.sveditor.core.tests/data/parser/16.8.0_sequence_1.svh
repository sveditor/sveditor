
module m;
	sequence s1;
	@(posedge clk) a ##1 b ##1 c;
	endsequence
	sequence s2;
	@(posedge clk) d ##1 e ##1 f;
	endsequence
	sequence s3;
	@(negedge clk) g ##1 h ##1 i;
	endsequence
	sequence s4;
	@(edge clk) j ##1 k ##1 l;
	endsequence
endmodule