
module m;
	sequence sub_seq2(lv);
		(a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
	endsequence
	sequence seq2;
		int v1;
		c ##1 sub_seq2(v1) // v1 is bound to lv
		##1 (do1 == v1); // v1 holds the value that was assigned to lv
	endsequence	
	
endmodule
