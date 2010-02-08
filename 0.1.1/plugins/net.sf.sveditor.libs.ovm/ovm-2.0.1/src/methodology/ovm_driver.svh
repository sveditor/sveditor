// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_driver.svh#17 $
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


class ovm_driver #(type REQ = ovm_sequence_item,
                   type RSP = REQ) extends ovm_component;

  ovm_seq_item_pull_port #(REQ, RSP) seq_item_port;
  ovm_seq_item_pull_port #(REQ, RSP) seq_item_prod_if;

  ovm_analysis_port #(RSP) rsp_port;

  REQ req;
  RSP rsp;

  function new (string name, ovm_component parent);
    super.new(name, parent);
    seq_item_port    = new("sqr_pull_port", this);
    seq_item_prod_if = seq_item_port;
    rsp_port    = new("rsp_port", this);
  endfunction // new

  task run();
    return;
  endtask // run

endclass

