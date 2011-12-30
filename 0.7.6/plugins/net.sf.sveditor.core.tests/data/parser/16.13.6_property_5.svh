
module m;
	property p16_nested;
		(write_en & data_valid) |->
		(write_en && (retire_address[0:4]==addr)) [*2] |->
			##[3:8] write_en && !data_valid && (write_address[0:4]==addr);
	endproperty	
	
endmodule