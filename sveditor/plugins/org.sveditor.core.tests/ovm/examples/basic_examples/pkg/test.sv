// $Id: test.sv,v 1.15 2009/05/01 14:34:38 redelman Exp $
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
module test;
  import ovm_pkg::*;

  //--------------------------------------------------------------------
  // lower
  //--------------------------------------------------------------------
  class lower extends ovm_component;
    int data;
    string str;

    function new (string name, ovm_component parent);
      super.new(name, parent);
    endfunction

    task run();
      $display("%0t: %m: start run", $time);
      #10 $display("%0t: %s HI", $time, get_full_name());
    endtask

    function string get_type_name();
      return "lower";
    endfunction

    function void build();
       void'(get_config_int("data", data));
       void'(get_config_string("str", str));
    endfunction 

    function void do_print(ovm_printer printer);
      printer.print_field("data", data, 32);
      printer.print_string("str", str);
    endfunction
  endclass

  //--------------------------------------------------------------------
  // myunit
  //--------------------------------------------------------------------
  class myunit extends ovm_component;
   lower l1;
   lower l2;
   int a[];

    function new (string name, ovm_component parent);
      super.new(name, parent);
      l1 = new ("l1", this);
      l2 = new ("l2", this);
      set_config_string("l1", "str", "hi");
      set_config_int("*", "da*", 'h100);
      l1.data = 'h30;
      l2.data = 'h40;
      a = new[5]; for(int i=0; i<5;++i) a[i] = i*i;
    endfunction

    task run();
      #10 $display("%0t: %s HI", $time, get_full_name());
    endtask

    function string get_type_name();
      return "myunit";
    endfunction

    function void do_print(ovm_printer printer);
      printer.print_array_header("a", a.size());
      for(int i=0; i<a.size(); ++i) 
        printer.print_field($psprintf("a[%0d]", i), a[i], 32, OVM_HEX, "[");
      printer.print_array_footer();
    endfunction
      
  endclass


  // Factory registration 

  //--------------------------------------------------------------------
  // lower_wrapper
  //--------------------------------------------------------------------
  class lower_wrapper extends ovm_object_wrapper;
  
    function ovm_component create_component(string name, ovm_component parent);
      lower u;
      u = new(name, parent);
      return u;
    endfunction
  
    function string get_type_name();
      return "lower";
    endfunction
  
    static function bit register_me();
      lower_wrapper w; w = new;
      factory.register(w);
      return 1;
    endfunction

    static bit is_registered = register_me();
  endclass

  //--------------------------------------------------------------------
  // myunit_wrapper
  //--------------------------------------------------------------------
  class myunit_wrapper extends ovm_object_wrapper;

    function ovm_component create_component(string name, ovm_component parent);
      myunit u;
      u = new(name, parent);
      return u;
    endfunction

    function string get_type_name();
      return "myunit";
    endfunction

    static function bit register_me();
      myunit_wrapper w; w = new;
      factory.register(w);
      return 1;
    endfunction

    static bit is_registered = register_me();
  endclass

  myunit mu = new("mu", null);

  //--------------------------------------------------------------------
  // mydata
  //--------------------------------------------------------------------
`ifdef INCA
  class mydata extends ovm_object;
    `ovm_object_utils(mydata)
  endclass
`else
  class mydata extends ovm_object;
    function ovm_object create(string name);
      mydata d; d=new; d.set_name(name);
      return d;
    endfunction // ovm_object
    function string get_type_name();
      return "mydata";
    endfunction
  endclass

  //--------------------------------------------------------------------
  // mydata_wrapper
  //--------------------------------------------------------------------
  class mydata_wrapper extends ovm_object_wrapper;

    function ovm_object create_object(string name="");
      mydata u;
      u = new;
      if(name !="") u.set_name(name);
      return u;
    endfunction

    function string get_type_name();
      return "myobject";
    endfunction

    static function bit register_me();
      mydata_wrapper w; w = new;
      factory.register(w);
      return 1;
    endfunction

    static bit is_registered = register_me();
  endclass
`endif 

  mydata bar = new;

  initial begin
    set_config_int("mu.*", "data", 101);
    set_config_string("mu.*", "str", "hi");
    set_config_int("mu.l1", "data", 55);
    set_config_object("mu.*", "obj", bar);
    mu.print_config_settings("", null, 1);
    ovm_default_printer = ovm_default_tree_printer;
    mu.print();
    factory.print(1);
    run_test();
    mu.print();
  end
  initial
    #5 mu.l1.kill();
  initial
    #10 ovm_top.stop_request();
endmodule
