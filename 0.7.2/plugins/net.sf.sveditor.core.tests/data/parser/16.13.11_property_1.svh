
module m;
	initial a1: assume property( @(posedge clk) reset[*5] #=# always !reset);
	
	property p1;
		a ##1 b |=> always c;
	endproperty
	
	property p2;
		always [2:5] a;
	endproperty
	property p3;
		s_always [2:5] a;
	endproperty
	property p4;
		always [2:$] a;
	endproperty
	property p5;
		s_always [2:$] a; // Illegal
	endproperty	
	
endmodule