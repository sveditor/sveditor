${file_header}
class ${name}_driver extends uvm_driver #(${name}_seq_item);

	`uvm_component_utils(${name}_driver)
	
	function new(string name, uvm_component parent=null);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction
	
	task run_phase(uvm_phase phase);
		${name}_seq_item		item;
		
		forever begin
			seq_item_port.get_next_item(item);
			// TODO: execute the sequence item
			seq_item_port.item_done();
		end
	endtask
endclass
