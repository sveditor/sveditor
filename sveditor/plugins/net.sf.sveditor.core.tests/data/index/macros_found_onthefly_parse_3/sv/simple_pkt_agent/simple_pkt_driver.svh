

class simple_pkt_driver extends uvm_driver #(simple_pkt_seq_item);

	`uvm_component_utils(simple_pkt_driver)
	
	const string report_id = "simple_pkt_driver";
	
	uvm_analysis_port #(simple_pkt_seq_item)		ap;
	
	simple_pkt_config								m_cfg;
	
	function new(string name, uvm_component parent=null);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		ap = new("ap", this);
		
		m_cfg = simple_pkt_config::get_config(this);
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction
	
	static int total_count;
	
	task run_phase(uvm_phase phase);
		simple_pkt_seq_item		item;
		
		forever begin
			seq_item_port.get_next_item(item);
			// TODO: execute the sequence item
			item.print();
			
			// Send the item to the analysis port
			ap.write(item);
			`uvm_info("DRIVER", $psprintf("Received item %0d", total_count), UVM_MEDIUM);
			total_count++;
			
			#100;
			
			seq_item_port.item_done();
		end
	endtask
endclass



