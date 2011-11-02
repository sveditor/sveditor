
module m;
	sequence s1(w, x, y);
	w ##1 x ##[2:10] y;
	endsequence
	sequence s2(w, y, bit x);
	w ##1 x ##[2:10] y;
	endsequence
	
	s1(.w(a), .x(bit'(b)), .y(c))
	s2(.w(a), .x(b), .y(c))	
endmodule