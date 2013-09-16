
class multi_port_shared_cov_env extends uvm_env;
	
	`uvm_component_utils(multi_port_shared_cov_env)
	
	simple_pkt_agent						a1;
	simple_pkt_agent						a2;
	simple_pkt_agent						a3;
	simple_pkt_agent						a4;
	
	/****************************************************************
	 * Data Fields
	 ****************************************************************/
	
	/****************************************************************
	 * new()
	 ****************************************************************/
	function new(string name, uvm_component parent=null);
		super.new(name, parent);
	endfunction

	/****************************************************************
	 * build_phase()
	 ****************************************************************/
	function void build_phase(uvm_phase phase);
		simple_pkt_config cfg = simple_pkt_config::type_id::create("cfg");
		super.build_phase(phase);
	
		uvm_config_db #(simple_pkt_config)::set(this, "*", "simple_pkt_config", cfg);
		
		a1 = simple_pkt_agent::type_id::create("a1", this);
		a2 = simple_pkt_agent::type_id::create("a2", this);
		a3 = simple_pkt_agent::type_id::create("a3", this);
		a4 = simple_pkt_agent::type_id::create("a4", this);
		
	endfunction

	/****************************************************************
	 * connect_phase()
	 ****************************************************************/
	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
	endfunction

	/****************************************************************
	 * run_phase()
	 ****************************************************************/
	task run_phase(uvm_phase phase);
		phase.raise_objection(this);

		phase.drop_objection(this);
	endtask
	
endclass



