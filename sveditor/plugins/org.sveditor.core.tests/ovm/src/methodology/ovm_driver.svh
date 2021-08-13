// $Id: ovm_driver.svh,v 1.17 2009/05/12 21:02:29 redelman Exp $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// CLASS: ovm_driver #(REQ,RSP)
//
// The base class for drivers that initiate requests for new transactions via
// a ovm_seq_item_pull_port. The ports are typically connected to the exports of
// an appropriate sequencer component.
//
// This driver operates in pull mode. Its ports are typically connected to the
// corresponding exports in a pull sequencer as follows:
//
//|    driver.seq_item_port.connect(sequencer.seq_item_export);
//|    driver.rsp_port.connect(sequencer.rsp_export);
//
// The ~rsp_port~ needs connecting only if the driver will use it to write
// responses to the analysis export in the sequencer.
//
//------------------------------------------------------------------------------

class ovm_driver #(type REQ=ovm_sequence_item,
                   type RSP=REQ) extends ovm_component;


  // Port: seq_item_port
  //
  // Derived driver classes should use this port to request items from the
  // sequencer. They may also use it to send responses back.

  ovm_seq_item_pull_port #(REQ, RSP) seq_item_port;

  ovm_seq_item_pull_port #(REQ, RSP) seq_item_prod_if; // alias

  // Port: rsp_port
  //
  // This port provides an alternate way of sending responses back to the
  // originating sequencer. Which port to use depends on which export the
  // sequencer provides for connection.

  ovm_analysis_port #(RSP) rsp_port;

  REQ req;
  RSP rsp;

  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);
    seq_item_port    = new("sqr_pull_port", this);
    rsp_port         = new("rsp_port", this);
    seq_item_prod_if = seq_item_port;
  endfunction // new

  const static string type_name = "ovm_driver #(REQ,RSP)";

  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass

