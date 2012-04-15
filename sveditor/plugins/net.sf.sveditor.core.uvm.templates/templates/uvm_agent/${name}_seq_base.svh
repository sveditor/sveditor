${file_header}
`ifndef INCLUDED_${filename}_SVH
`define INCLUDED_${filename}_SVH

class ${name}_seq_base extends uvm_sequence #(${name}_seq_item);
	`uvm_object_utils(${name}_seq_base);
	
	string report_id = "${name}_seq_base";
	
	function new(string name="${name}_seq_base");
		super.new(name);
	endfunction
	
	task body();
		`uvm_error(report_id, "base-class body task not overridden");
	endtask
	
endclass

`endif /* INCLUDED_${filename}_SVH */
