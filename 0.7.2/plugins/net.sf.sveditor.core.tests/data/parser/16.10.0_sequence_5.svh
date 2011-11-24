
module m;

	sequence seq2a;
		int v1; c ##1 sub_seq2(v1).triggered ##1 (do1 == v1); // v1 is now bound to lv
	endsequence
	
endmodule
