// $Id: xbus_slave_monitor.sv,v 1.17 2009/10/30 15:29:21 jlrose Exp $
//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

`ifndef XBUS_SLAVE_MONITOR_SV
`define XBUS_SLAVE_MONITOR_SV

//------------------------------------------------------------------------------
//
// CLASS: xbus_slave_monitor
//
//------------------------------------------------------------------------------

class xbus_slave_monitor extends ovm_monitor;

  // This property is the virtual interface needed for this component to drive
  // and view HDL signals.
  protected virtual xbus_if xsi;

  // The following two unsigned integer properties are used by
  // check_addr_range() method to detect if a transaction is for this target.
  protected int unsigned min_addr = 16'h0000;
  protected int unsigned max_addr = 16'hFFFF;

  // The following two bits are used to control whether checks and coverage are
  // done both in the monitor class and the interface.
  bit checks_enable = 1;
  bit coverage_enable = 1;

  ovm_analysis_port#(xbus_transfer) item_collected_port;
  ovm_blocking_peek_imp#(xbus_transfer,xbus_slave_monitor) addr_ph_imp;

  // The following property holds the transaction information currently
  // begin captured (by the collect_address_phase and data_phase methods). 
  protected xbus_transfer trans_collected;

  // monitor notifier that the address phase (and full item) has been collected
  protected event address_phase_grabbed;

  // Events needed to trigger covergroups
  protected event cov_transaction;
  protected event cov_transaction_beat;

  // Fields to hold trans data and wait_state.  No coverage of dynamic arrays.
  protected bit [15:0] addr;
  protected bit [7:0] data;
  protected int unsigned wait_state;

  // Transfer collected covergroup
  covergroup cov_trans @cov_transaction;
    option.per_instance = 1;
    trans_start_addr : coverpoint trans_collected.addr {
      option.auto_bin_max = 16; }
    trans_dir : coverpoint trans_collected.read_write;
    trans_size : coverpoint trans_collected.size {
      bins sizes[] = {1, 2, 4, 8};
      illegal_bins invalid_sizes = default; }
    trans_addrXdir : cross trans_start_addr, trans_dir;
    trans_dirXsize : cross trans_dir, trans_size;
  endgroup : cov_trans

  // Transfer collected data covergroup
  covergroup cov_trans_beat @cov_transaction_beat;
    option.per_instance = 1;
    beat_addr : coverpoint addr {
      option.auto_bin_max = 16; }
    beat_dir : coverpoint trans_collected.read_write;
    beat_data : coverpoint data {
      option.auto_bin_max = 8; }
    beat_wait : coverpoint wait_state {
      bins waits[] = { [0:9] };
      bins others = { [10:$] }; }
    beat_addrXdir : cross beat_addr, beat_dir;
    beat_addrXdata : cross beat_addr, beat_data;
  endgroup : cov_trans_beat

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils_begin(xbus_slave_monitor)
    `ovm_field_int(min_addr, OVM_ALL_ON)
    `ovm_field_int(max_addr, OVM_ALL_ON)
    `ovm_field_int(checks_enable, OVM_ALL_ON)
    `ovm_field_int(coverage_enable, OVM_ALL_ON)
  `ovm_component_utils_end

  // new - constructor
  function new(string name, ovm_component parent=null);
    super.new(name, parent);
    cov_trans = new();
    cov_trans.set_inst_name({get_full_name(), ".cov_trans"});
    cov_trans_beat = new();
    cov_trans_beat.set_inst_name({get_full_name(), ".cov_trans_beat"});
    trans_collected = new();
    item_collected_port = new("item_collected_port", this);
    addr_ph_imp = new("addr_ph_imp", this);
  endfunction : new

  // assign the virtual interface
  function void assign_vi(virtual interface xbus_if xsi);
    this.xsi = xsi;
  endfunction : assign_vi

  // set the monitor's address range
  function void set_addr_range(bit [15:0] min_addr, bit [15:0] max_addr);
    this.min_addr = min_addr;
    this.max_addr = max_addr;
  endfunction : set_addr_range

  // get the monitor's min addr
  function bit [15:0] get_min_addr();
    return min_addr;
  endfunction : get_min_addr

  // get the monitor's max addr
  function bit [15:0] get_max_addr();
    return max_addr;
  endfunction : get_max_addr

  // run phase
  virtual task run();
    fork
      collect_transactions();
    join
  endtask : run

  // collect_transactions
  virtual protected task collect_transactions();
    bit range_check;
    forever begin
      if (m_parent != null)
        trans_collected.slave = m_parent.get_name();
      collect_address_phase();
      range_check = check_addr_range();
      if (range_check) begin
        void'(this.begin_tr(trans_collected));
        -> address_phase_grabbed;
        collect_data_phase();
        `ovm_info(get_type_name(), $psprintf("Transfer collected :\n%s",
          trans_collected.sprint()), OVM_FULL)
        if (checks_enable)
          perform_transfer_checks();
        if (coverage_enable)
          perform_transfer_coverage();
        item_collected_port.write(trans_collected);
      end
    end
  endtask : collect_transactions

  // check_addr_range
  virtual protected function bit check_addr_range();
    if ((trans_collected.addr >= min_addr) &&
      (trans_collected.addr <= max_addr)) begin
      return 1;
    end
    return 0;
  endfunction : check_addr_range

  // collect_address_phase
  virtual protected task collect_address_phase();
    @(posedge xsi.sig_clock iff ( (xsi.sig_read === 1) || 
      (xsi.sig_write === 1) ) );
    trans_collected.addr = xsi.sig_addr;
    case (xsi.sig_size)
      2'b00 : trans_collected.size = 1;
      2'b01 : trans_collected.size = 2;
      2'b10 : trans_collected.size = 4;
      2'b11 : trans_collected.size = 8;
    endcase
    trans_collected.data = new[trans_collected.size];
    case ({xsi.sig_read,xsi.sig_write})
      2'b00 : trans_collected.read_write = NOP;
      2'b10 : trans_collected.read_write = READ;
      2'b01 : trans_collected.read_write = WRITE;
    endcase
  endtask : collect_address_phase

  // collect_data_phase
  virtual protected task collect_data_phase();
    if (trans_collected.read_write != NOP) begin
      for (int i = 0; i < trans_collected.size; i++) begin
        @(posedge xsi.sig_clock iff xsi.sig_wait === 0);
        trans_collected.data[i] = xsi.sig_data;
      end
    end
    this.end_tr(trans_collected);
  endtask : collect_data_phase

  // perform_transfer_checks
  protected function void perform_transfer_checks();
    check_transfer_size();
    check_transfer_data_size();
  endfunction : perform_transfer_checks

  // check_transfer_size
  protected function void check_transfer_size();
    check_transfer_size : assert(trans_collected.size == 1 || 
      trans_collected.size == 2 || trans_collected.size == 4 || 
      trans_collected.size == 8) else begin
      `ovm_error(get_type_name(),
        "Invalid transfer size!")
    end
  endfunction : check_transfer_size

  // check_transfer_data_size
  protected function void check_transfer_data_size();
    if (trans_collected.size != trans_collected.data.size())
      `ovm_error(get_type_name(),
        "Transfer size field / data size mismatch.")
  endfunction : check_transfer_data_size

  // perform_transfer_coverage
  protected function void perform_transfer_coverage();
    -> cov_transaction;
    for (int unsigned i = 0; i < trans_collected.size; i++) begin
      addr = trans_collected.addr + i;
      data = trans_collected.data[i];
      wait_state = trans_collected.wait_state[i];
      -> cov_transaction_beat;
    end
  endfunction : perform_transfer_coverage

  task peek(output xbus_transfer trans);
    @address_phase_grabbed;
    trans = trans_collected;
  endtask : peek

endclass : xbus_slave_monitor

`endif // XBUS_SLAVE_MONITOR_SV

