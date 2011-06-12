/****************************************************************************
 * uvm_monitor.svh
 ****************************************************************************/

class @name@_monitor extends uvm_monitor;
	
	uvm_analysis_port #(@name@_seq_item)			ap;
	
	@name@_config									m_cfg;
	
	`uvm_component_utils(@name@_monitor)
	
	function new(string name, uvm_component parent);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		m_cfg = @name@_config::get_config(this, "@name@_config");
		
	endfunction
	
	function void connect_phase(uvm_phase phase);
		super.connnect_phase(phase);
		
	endfunction
	
	function void end_of_elaboration_phase(uvm_phase phase);
		print_config();
	endfunction
	
	task run_phase(uvm_phase phase);
		// TODO: implement @name@_monitor run_phase
	endtask
	
	
endclass
