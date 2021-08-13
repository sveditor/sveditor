
`ifndef INCLUDED_simple_pkt_seq_base_SVH
`define INCLUDED_simple_pkt_seq_base_SVH

class simple_pkt_seq_base extends uvm_sequence #(simple_pkt_seq_item);
	`uvm_object_utils(simple_pkt_seq_base);
	
	static const string report_id = "simple_pkt_seq_base";
	
	function new(string name="simple_pkt_seq_base");
		super.new(name);
	endfunction
	
	task body();
		`uvm_error(report_id, "base-class body task not overridden");
	endtask
	
endclass

`endif /* INCLUDED_simple_pkt_seq_base_SVH */



