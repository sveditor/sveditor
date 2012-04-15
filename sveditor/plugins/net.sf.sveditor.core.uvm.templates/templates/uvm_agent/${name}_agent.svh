${file_header}
class ${name}_agent extends uvm_agent;
	
${name}_driver						m_driver;
uvm_sequencer #(${name}_seq_item)	m_seqr;
	
function new(string name, uvm_component parent=null);
super.new(name, parent);
endfunction
	
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
	endfunction

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		
		m_driver.seq_item_port.connect(m_seqr.seq_item_export);
	endfunction

endclass
