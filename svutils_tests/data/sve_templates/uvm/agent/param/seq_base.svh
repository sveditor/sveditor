

class ${name}_seq_base `${name}_plist extends uvm_sequence #(${name}_seq_item);
	typedef ${name}_seq_base `${name}_params this_t;
	`uvm_object_param_utils(this_t)
	
	static const string report_id = "${name}_seq_base";
	
	function new(string name="${name}_seq_base");
		super.new(name);
	endfunction
	
	task body();
		`uvm_error(report_id, "base-class body task not overridden");
	endtask
	
endclass



