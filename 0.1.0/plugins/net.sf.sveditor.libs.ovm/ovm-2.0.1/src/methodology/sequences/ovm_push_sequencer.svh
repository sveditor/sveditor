//----------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
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


typedef class ovm_sequence_base;

class ovm_push_sequencer #(type REQ = ovm_sequence_item,
                           type RSP = REQ) extends ovm_sequencer_param_base #(REQ, RSP);

  typedef ovm_push_sequencer #( REQ , RSP) this_type;

  ovm_blocking_put_port #(REQ) req_port;

  function new (string name, ovm_component parent);
    super.new(name, parent);

    req_port              = new ("req_port", this);
  endfunction // new

  protected virtual function int  m_find_number_driver_connections();
    return(req_port.size());
  endfunction

  task run();
    REQ t;
    integer selected_sequence;

    fork
      super.run();
      forever
	begin
          do 
            begin
              wait_for_sequences();
              selected_sequence = choose_next_request();
              if (selected_sequence == -1) begin
		wait_for_available_sequence();
              end
            end while (selected_sequence == -1);
          // issue grant
          if (selected_sequence >= 0) begin
            set_arbitration_completed(arb_sequence_q[selected_sequence].request_id);
            arb_sequence_q.delete(selected_sequence);
            m_update_lists();
          end
          m_req_fifo.get(t);
          req_port.put(t);
          m_wait_for_item_sequence_id = t.get_sequence_id();
          m_wait_for_item_transaction_id = t.get_transaction_id();
	end // forever begin
    join
  endtask
endclass
