// $Id: xbus_master_agent.sv,v 1.10 2009/05/01 14:34:38 redelman Exp $
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

`ifndef XBUS_MASTER_AGENT_SV
`define XBUS_MASTER_AGENT_SV

virtual class foo; endclass

virtual class foobar;
endclass

//------------------------------------------------------------------------------
//
// CLASS: xbus_master_agent
//
//------------------------------------------------------------------------------

class xbus_master_agent extends ovm_agent;

  protected ovm_active_passive_enum is_active = OVM_ACTIVE;
  protected int master_id;

  xbus_master_driver driver;
  xbus_master_sequencer sequencer;
  xbus_master_monitor monitor;

  // Provide implementations of virtual methods such as get_type_name and create
  `ovm_component_utils_begin(xbus_master_agent)
    `ovm_field_enum(ovm_active_passive_enum, is_active, OVM_ALL_ON)
    `ovm_field_int(master_id, OVM_ALL_ON)
  `ovm_component_utils_end

  // new - constructor
  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction : new

  // build
  function void build();
    super.build();
    monitor = xbus_master_monitor::type_id::create("monitor", this);
    if(is_active == OVM_ACTIVE) begin
      sequencer = xbus_master_sequencer::type_id::create("sequencer", this);
      driver = xbus_master_driver::type_id::create("driver", this);
    end
  endfunction : build

  // connect
  function void connect();
    if(is_active == OVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction : connect

  // assign the virtual interfaces of the agent's children
  function void assign_vi(virtual interface xbus_if xmi);
    monitor.assign_vi(xmi);
    if (is_active == OVM_ACTIVE) begin
      sequencer.assign_vi(xmi);
      driver.assign_vi(xmi);
    end
  endfunction : assign_vi

endclass : xbus_master_agent

`endif // XBUS_MASTER_AGENT_SV

