import ovm_pkg::*;

`ifndef T1_SV
`define T1_SV

`include "ovm_macros.svh"
`include "t2.sv"

class t1 extends ovm_object;
   int mem1;

   `ovm_object_utils(t1)
   
   function new(string name = "t1");
      super.new(name);
   endfunction // new

endclass // t1

`endif
