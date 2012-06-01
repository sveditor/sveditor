${file_header}
class ${name}_seq_item extends uvm_sequence_item;
	`uvm_object_utils(${name}_seq_item)
	
	// TODO: Declare fields here
	
	function new(string name="${name}_seq_item");
		super.new(name);
	endfunction
	
	
endclass

${file_footer}

