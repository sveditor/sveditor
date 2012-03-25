
module m;
	time t;
		
	always @(posedge clk)
		if (state == REQ)
			assert (req1 || req2)
		else begin
			t = $time;
			#5 $error("assert failed at time %0t",t);
		end
		
endmodule