
module m;

	sequence seq2b;
		int v1; c ##1 !sub_seq2(v1).triggered ##1 (do1 == v1); // v1 unassigned
	endsequence

endmodule
