${file_header}
`ifndef INCLUDED_${name}_seq_base_SVH
`define INCLUDED_${name}_seq_base_SVH

class ${name}_seq_base extends uvm_sequence #(${name}_seq_item);
	`uvm_object_utils(${name}_seq_base);
	
	static const string report_id = "${name}_seq_base";
	
	function new(string name="${name}_seq_base");
		super.new(name);
	endfunction
	
	task body();
		`uvm_error(report_id, "base-class body task not overridden");
	endtask
	
endclass

`endif /* INCLUDED_${name}_seq_base_SVH */

${file_footer}

