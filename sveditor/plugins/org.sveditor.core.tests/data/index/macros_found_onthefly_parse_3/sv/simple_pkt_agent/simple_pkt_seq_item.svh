


class simple_pkt_seq_item extends uvm_sequence_item;
	`uvm_object_utils(simple_pkt_seq_item)
	
	const string report_id = "simple_pkt_seq_item";
	
	// TODO: Declare fields here
	rand pkt_type_t					pkt_type;
	rand bit[7:0]					len;
	
	function new(string name="simple_pkt_seq_item");
		super.new(name);
	endfunction

	// TODO: Declare do_print, do_compare, do_copy methods

	function void do_print(uvm_printer printer);
		if (printer.knobs.sprint == 0) begin
			$display(convert2string());
		end else begin
			printer.m_string = convert2string();
		end
	endfunction

	function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit ret = 1;
		simple_pkt_seq_item rhs_;
		
		if (!$cast(rhs_, rhs)) begin
			return 0;
		end
		
		ret &= super.do_compare(rhs, comparer);
		
		// TODO: implement comparison logic
	
		return ret;
	endfunction

	function void do_copy(uvm_object rhs);
		simple_pkt_seq_item rhs_;
		
		if (!$cast(rhs_, rhs)) begin
			`uvm_error(report_id, "Cast failed in do_copy()");
			return;
		end
		
		super.do_copy(rhs);
		
		// TODO: copy item-specific fields
		
	endfunction
			
endclass



