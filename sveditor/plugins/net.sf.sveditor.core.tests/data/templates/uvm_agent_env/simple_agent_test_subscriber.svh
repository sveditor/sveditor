

class simple_agent_test_subscriber extends uvm_subscriber #(simple_seq_item);
	`uvm_component_utils(simple_agent_test_subscriber)
	
	function new(string name, uvm_component parent=null);
		super.new(name, parent);
	endfunction
	
	virtual function void write(simple_seq_item t);
		simple_agent_test_seq_item item;
		
		$cast(item, t);
		
		$display("ITEM: A=%0d B=%0d", item.A, item.B);
	endfunction

endclass
