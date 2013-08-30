

class simple_pkt_monitor extends uvm_monitor;

	uvm_analysis_port #(simple_pkt_seq_item)			ap;
	
	simple_pkt_config									m_cfg;
	
	simple_pkt_seq_item									m_item;
	
	covergroup pkt_cg;
		type_cp : coverpoint m_item.pkt_type;
		
		len_cp : coverpoint m_item.len;
		
		lenXtype : cross type_cp, len_cp;
		
	endgroup
	
	const string report_id = "simple_pkt_monitor";
	
	`uvm_component_utils(simple_pkt_monitor)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	
		// Obtain the config object
		m_cfg = simple_pkt_config::get_config(this);
	
		// Create the analysis port
		ap = new("ap", this);

	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction
	
	task run_phase(uvm_phase phase);
		// TODO: implement simple_pkt_monitor run_phase
	endtask
	
	
endclass


