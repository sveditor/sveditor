// $Id: ovm_push_driver.svh,v 1.4 2008/08/29 11:06:49 jlrose Exp $
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


class ovm_push_driver #(type REQ = ovm_sequence_item,
                        type RSP = REQ) extends ovm_component;

typedef ovm_push_driver #(REQ, RSP) this_type;

  ovm_blocking_put_imp #(REQ, this_type) req_export;
  ovm_analysis_port #(RSP) rsp_port;

  REQ req;
  RSP rsp;

  function new (string name, ovm_component parent);
    super.new(name, parent);
    req_export    = new("req_export", this);
    rsp_port    = new("rsp_port", this);
  endfunction // new

  virtual function void build();
    super.build();
  endfunction // function

  function void check_port_connections();
    assert(req_export.size() == 1) else
    ovm_report_fatal("Connection Error",
                     $psprintf("Must connect to seq_item_port(%0d)",
                               req_export.size()));
  endfunction // void
  
  virtual function void end_of_elaboration();
    check_port_connections();
  endfunction // void
  
  virtual task put(REQ item);
    ovm_report_fatal("OVM_PUSH_DRIVER", "Put task for push driver is not implemented");
  endtask // put

endclass

