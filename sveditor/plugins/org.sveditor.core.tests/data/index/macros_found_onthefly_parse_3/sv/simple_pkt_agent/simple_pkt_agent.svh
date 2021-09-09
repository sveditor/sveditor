

/**
 * Class: simple_pkt_agent
 */
class simple_pkt_agent extends uvm_agent;

	`uvm_component_utils(simple_pkt_agent)

	const string report_id = "simple_pkt_agent";

	simple_pkt_driver								m_driver;
	uvm_sequencer #(simple_pkt_seq_item)			m_seqr;
	simple_pkt_monitor								m_monitor;
	
	uvm_analysis_port #(simple_pkt_seq_item)		m_mon_out_ap;
	uvm_analysis_port #(simple_pkt_seq_item)		m_drv_out_ap;
	
	simple_pkt_config								m_cfg;
	
	
	function new(string name, uvm_component parent=null);
		super.new(name, parent);
	endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	
		// Obtain the config object for this agent
		m_cfg = simple_pkt_config::get_config(this);
		
		if (m_cfg.has_driver) begin
			m_driver = simple_pkt_driver::type_id::create("m_driver", this);
			
			// Create driver analysis port
			m_drv_out_ap = new("m_drv_out_ap", this);
		end
		
		if (m_cfg.has_sequencer) begin
			m_seqr = new("m_seqr", this);
		end
	
		if (m_cfg.has_monitor) begin
			m_monitor = simple_pkt_monitor::type_id::create("m_monitor", this);
			
			// Create the monitor analysis port
			m_mon_out_ap = new("m_mon_out_ap", this);
		end
	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		
		// Connect the driver and sequencer
		if (m_cfg.has_driver && m_cfg.has_sequencer) begin
			m_driver.seq_item_port.connect(m_seqr.seq_item_export);
		end
		
		if (m_cfg.has_monitor) begin
			// Connect the monitor to the monitor AP
			m_monitor.ap.connect(m_mon_out_ap);
		end
		
		if (m_cfg.has_driver) begin
			// Connect the driver to the driver AP
			m_driver.ap.connect(m_drv_out_ap);
		end
		
	endfunction

endclass



