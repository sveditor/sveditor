

/**
 * Class: simple_pkt_config
 * Provides configuration information for agent simple_pkt
 */
class simple_pkt_config extends uvm_object;
	`uvm_object_utils(simple_pkt_config)
	
	static const string report_id = "simple_pkt_config";
	
	// TODO: Add virtual interface handles

	// Specify the config values
	bit					has_monitor		= 1;
	bit					has_driver		= 1;
	bit					has_sequencer	= 1;

	
	/**
	 * Function: get_config
	 * Convenience function that obtains the config object from the
	 * UVM configuration database and reports an error if not present
	 */
	static function simple_pkt_config get_config(
			uvm_component			comp,
			string					cfg_name = "simple_pkt_config");
		simple_pkt_config cfg = null;
		
		if (!uvm_config_db #(simple_pkt_config)::get(comp, "", cfg_name, cfg)) begin
			comp.uvm_report_error(report_id,
				$psprintf("%s has no config associated with id %s",
					comp.get_full_name(), cfg_name),, `__FILE__, `__LINE__);
			return null;
		/*
		 */
		end
		return cfg;
	endfunction

endclass



