module bob ();
   parameter BOB = 1;
   initial
      begin
         parameter BOB3 = 1;
      end
      
   task mytask();
      parameter BOB4 = 1;
      begin
         parameter BOB5 = 1; 
         logic i;
      end
   endtask

endmodule

module t4(o);
     output logic o;
endmodule

module bobby ();
   `include "parameters.sv"
   wire bob3;
   wire [1:0] #5 xadr_dly=bob3;
   wire [12:0] bob1;
   wire bob2;
   assign bob1 = top.mux.some_signal;
   assign bob1 = `TOP.mux.some_signal;
   assign bob1 = `MUX.some_signal;
   
   parameter Tu=5;
   parameter numAddrX=5;
   wire #Tu  ye_dly=bob1;
   wire [3:0] bob6 ;
   wire ye_tog=(bob1!==bob2);
   
endmodule

module top(a, b, c, d);    // 1
   input a;               // 2
   output reg b;              // 3
   input [7:0] c;         // 4
   output[11:0] d;        // 5
                        // 6
    wire [12:0] bus;       // 7
                        // 8
    always @ (a) begin     // 9
        b = ~a;            // 10
        case (1)
           1'b1: begin end
              default:
              begin
              end
        endcase
    end                 // 11

endmodule                    // 13


module gates();
   
   parameter myparam = 10;
  wire out0;
  wire out1;
  wire out2;
  wire (pull1, pull0)  #(1:2:3, 2:3:4, 4:5:6)  out5 = out2;
  wire (strong0, strong1) #myparam [10:0] out3 = '0;
  wire (supply0, supply1) #(1:2:3)        out4 = 1'b0;
  wire (weak0, weak1) #(1, 2, 4)          out6 = 1'b0;
  reg  in1,in2,in3,in4;

  
  always @*
     begin
     end

  not U1(out0,in1);
  and U2(out1,in1,in2,in3,in4);
  xor U3(out2,in1,in2,in3);
  initial begin
  $monitor(
  "in1=%b in2=%b in3=%b in4=%b out0=%b out1=%b out2=%b",
  in1,in2,in3,in4,out0,out1,out2); 
  in1 = 0;
  in2 = 0;
  in3 = 0;
  in4 = 0;
  #1 in1 = 1;
  #1 in2 = 1;
  #1 in3 = 1;
  #1 in4 = 1;
  #1 $finish;
  
  end 
endmodule

module top2 ();

`include "parameters.sv"
   `define BOB jane

parameter tck_delay = 0;
wire pad_an12_r;
wire #tck_delay pad_an12 = pad_an12_r; 
wire (pull1, pull0) #tck_delay [10:0] pad_an2 = pad_an12_r; 
tri (pull1, pull0) #tck_delay [10:0] pad_an23 = pad_an12_r; 

logic clk;
logic data_out;
logic data_in;
logic reset;
logic dout, bufifctrl;

wire #0 pad_an13 = pad_an12_r;

wire bob;
assign bob = top.reset;

	// The following buffers provide support for the UNUSED pin functions.
bufif1 (weak1, highz0) (dout, 1'b1, bufifctrl );
bufif1 (weak0, highz1) (dout, 1'b0, bufifctrl );
bufif1                 (dout, 1'b1, bufifctrl );

logic background1 , background2 , mode_var , pat_var , rw_state, mbist_active_background, md_wOs_wrOw;

task bobb ();
   endtask
   function fctn ();
   endfunction
initial
begin
   data_in = `SOME_DEFINE;
   clk = 1'b0;
   reset = 1'b1;

   #100; 
   reset = 1'b0;
   # 100;
   clk = 1'b1;
   #100;
   clk = 1'b0;
end

macro1 m1 (
      .clk,
      .data_in,
      .reset,
      .data_out
      );
      
always @* begin end
generate
endgenerate

endmodule

module my_module();
	event some_event;
   logic bob;
	initial
	begin
		->  some_event; // passes
		->>      some_event; // passes
		->> #2ns some_event; // passes
//		->> repeat (10) @(posedge bob) some_event; // passes
		->> @(posedge bob) some_event; // passes
	end
endmodule



module my_module(input logic some_input, output logic DOUT);

logic DOUT_i, normal_read_access;
specify
specparam Tdh = 10,
Tacc = 10;
// specify some delay
if (normal_read_access) (posedge some_input => (DOUT:DOUT_i)) = (Tacc, Tacc,Tdh); // unpexpected if statement
endspecify

endmodule
