import ovm_pkg::*;

`ifndef T2_SV
`define T2_SV

`include "ovm_macros.svh"
`include "t1.sv"

class t2 extends ovm_object;
   int mem1;

   `ovm_object_utils(t2)
   
   function new(string name = "t2");
      super.new(name);
   endfunction // new
   
endclass // t2

`endif
