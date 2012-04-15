${file_header}
`include "uvm_macros.svh"

package ${name}_agent_pkg;
	import uvm_pkg::*;
	
	`include "${name}_config.svh"
	`include "${name}_seq_item.svh"
	`include "${name}_driver.svh"
	`include "${name}_monitor.svh"
	`include "${name}_seq_base.svh"
	`include "${name}_agent.svh"
endpackage
