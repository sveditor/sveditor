module my_module #( 
		parameter PARAMETER_1 = 1, // this is parameter 1 parameter 
		PARAMETER_2 = 10 // this is parameter 2 
		) ( 
		input logic clk , // fixed 4MHz input clock 
		input logic [1:0] write_enable, // write_enable 
		input logic [1:0] read_enable, // read_enable 
		input logic [15:0]write_data , // write data 
		output logic [15:0] read_data // read data
		); 


	timeunit 1ns; // ERROR: Not recognizing time 
	timeprecision 1ps; // ERROR not recognizing time 

	logic [15:0] word_0; 
	logic [15:0] word_1; 

	localparam logic [15:0] TMR_SPB_ADDRL [PARAMETER_1 :0] = { 16'h1600, 16'h1400 }; // ERROR: Crazy parameter construct 

	property read_and_write_not_back_to_back; 
	@(posedge clk) 
	write_enable |=> !read-enable; 
	endproperty // ERROR: Doesn't recognize endproperty - expecting endmodule 
	ap_read_and_write_not_back_to_back: assert property (read_and_write_not_back_to_back); 
	cp_read_and_write_not_back_to_back: cover property (read_and_write_not_back_to_back); 

endmodule
