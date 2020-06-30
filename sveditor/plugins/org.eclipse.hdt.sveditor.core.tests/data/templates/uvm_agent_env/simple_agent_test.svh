
class simple_agent_test extends uvm_test;
	`uvm_component_utils(simple_agent_test)
	
	simple_agent							m_agent;
	simple_agent_test_subscriber			m_subscriber;
	
	
	function new(string name, uvm_component parent=null);
		super.new(name, parent);
	endfunction

	function void build_phase(uvm_phase phase);
		simple_config cfg = simple_config::type_id::create();
		
		uvm_config_db #(simple_config)::set(this, "*", 
				"simple_config", cfg);
				
		super.build_phase(phase);

		
		m_agent = simple_agent::type_id::create("m_agent", this);
		m_subscriber = simple_agent_test_subscriber::type_id::create("m_subscriber", this);

	endfunction	

	function void connect_phase(uvm_phase phase);
		m_agent.m_drv_out_ap.connect(m_subscriber.analysis_export);
	endfunction	

	task run_phase(uvm_phase phase);
		simple_agent_test_seq seq = simple_agent_test_seq::type_id::create("seq");
		
		phase.raise_objection(this, "Main");
		seq.start(m_agent.m_seqr);
		phase.drop_objection(this, "Main");
	endtask
	
endclass
