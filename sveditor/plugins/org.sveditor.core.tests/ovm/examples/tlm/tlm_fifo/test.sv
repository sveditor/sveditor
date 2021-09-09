
// $Id: test.sv,v 1.11 2009/05/01 14:34:38 redelman Exp $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------


/*
About: tlm_fifo

This test case supposed to test a producer consumer connection through a tlm_fifo of 10 levels.



Walk through the test:
Inside a module, there will be two threads established, the first one the *producer* will put a packet of an integer to put port, the second one *consumer* will get this packet through a get port. The put and get ports will be connected to the tlm_fifo exports. 

the method *fifo.used* will be used here to display which fifo level is used.

*/



module test;
  `ifdef INCA
    `include "ovm.svh"
  `else
    import ovm_pkg::*;
  `endif

  class packet;
    int i;
    function new(int v); i=v; endfunction
  endclass

  class producer extends ovm_component;
    ovm_put_port #(packet) data_out;
    function new(string name, ovm_component parent);
      super.new(name,parent);
      data_out = new("data_out", this);
    endfunction
    task run();
      packet p, pp;
      #1 p=new(0);
      while(data_out.try_put(p)) begin 
        $display("%0t: put data %0d", $time, p.i);
        #10 p = new(p.i+1);
      end
      $display("try_put status return: %0d", p.i);
      $display("%0t: do a blocking put", $time);
      data_out.put(p);
      $display("%0t: blocking put succeeded", $time);
    endtask
  endclass
  class consumer extends ovm_component;
    ovm_get_port #(packet) data_in;
    function new(string name, ovm_component parent);
      super.new(name,parent);
      data_in = new("data_in", this);
    endfunction
    task run();
      packet p;
      #100;  // fifo will fill up
      $display("%0t: getting one", $time);
      data_in.get(p);
      $display("%0t: recieved data %0d", $time, p.i);
      #100;  // let the blocking put succeed
      while(data_in.try_get(p)) begin
        $display("%0t: recieved data %0d", $time, p.i);
        #10;
      end
    endtask
  endclass

  producer prod = new("prod", null);
  consumer cons = new("cons", null);
  tlm_fifo #(packet) fifo = new("fifo", null, 10);

  initial begin
    prod.data_out.connect(fifo.put_export);
    cons.data_in.connect(fifo.get_export);

    fork
      run_test();
      repeat(30) begin
        $display("%0t:   FIFO level %0d of %0d", $time, fifo.used(), fifo.size());
        #10;
      end
      #5us global_stop_request();
    join
  end

endmodule
