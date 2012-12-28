${file_header}

class ${name}_monitor extends uvm_monitor;

	uvm_analysis_port #(${name}_seq_item)			ap;
	
	${name}_config									m_cfg;
	
	const string report_id = "${name}_monitor";
	
	`uvm_component_utils(${name}_monitor)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	
		// Obtain the config object
		m_cfg = ${name}_config::get_config(this);
	
		// Create the analysis port
		ap = new("ap", this);

	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction
	
	task run_phase(uvm_phase phase);
		// TODO: implement ${name}_monitor run_phase
	endtask
	
	
endclass

${file_footer}
