${file_header}
class ${name} extends uvm_sequence #(uvm_sequence_item);
	
	`uvm_object_utils(${name})
	
	/****************************************************************
	 * new()
	 ****************************************************************/
	function new(string name="${name}");
		super.new(name);
	endfunction
	
	/****************************************************************
	 * body()
	 ****************************************************************/
	task body();
		
	endtask

endclass

${file_footer}

