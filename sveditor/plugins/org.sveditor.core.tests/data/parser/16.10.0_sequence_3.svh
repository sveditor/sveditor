
module m;
	sequence sub_seq1;
		int v1;
		(a ##1 !a, v1 = data_in) ##1 !b[*0:$] ##1 b && (data_out == v1);
	endsequence
	sequence seq1;
		c ##1 sub_seq1 ##1 (do1 == v1); // error because v1 is not visible
	endsequence
endmodule

