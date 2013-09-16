
`include "uvm_macros.svh"

package simple_pkt_agent_pkg;
	import uvm_pkg::*;
	
	typedef enum {
		PKT_TYPE_1,
		PKT_TYPE_2,
		PKT_TYPE_3,
		PKT_TYPE_4
	} pkt_type_t;
	
	`include "simple_pkt_config.svh"
	`include "simple_pkt_seq_item.svh"
	`include "simple_pkt_driver.svh"
	`include "simple_pkt_monitor.svh"
	`include "simple_pkt_seq_base.svh"
	`include "simple_pkt_agent.svh"
endpackage



