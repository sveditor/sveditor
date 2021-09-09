

class simple_agent_test_seq extends simple_seq_base;
	`uvm_object_utils(simple_agent_test_seq)
	
	virtual task body();
		simple_agent_test_seq_item item = simple_agent_test_seq_item::type_id::create();
		
		for (int i=0; i<10; i++) begin
			start_item(item);
			
			item.A = i;
			item.B = (i+5);
			
			finish_item(item);
		end
		
	endtask

endclass
