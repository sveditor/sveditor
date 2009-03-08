// $Id: sqr_ifs.svh,v 1.3 2008/10/09 14:59:10 jlrose Exp $
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


//----------------------------------------------------------------------
// sequencer interfaces
//----------------------------------------------------------------------

`define SEQ_ITEM_TASK_ERROR "Sequencer interface task not implemented"
`define SEQ_ITEM_FUNCTION_ERROR "Sequencer interface function not implemented"

//----------------------------------------------------------------------
// ovm_sqr_pull_if
//----------------------------------------------------------------------
virtual class sqr_if_base #(type T1=ovm_object, T2=T1);

  virtual task get_next_item(output T1 t);
    ovm_report_error("get_next_item", `SEQ_ITEM_TASK_ERROR);
  endtask

  virtual task try_next_item(output T1 t);
    ovm_report_error("try_next_item", `SEQ_ITEM_TASK_ERROR);
  endtask

  virtual function void item_done(input T2 t = null);
    ovm_report_error("item_done", `SEQ_ITEM_FUNCTION_ERROR);
  endfunction

  virtual task wait_for_sequences();
    ovm_report_error("wait_for_sequences", `SEQ_ITEM_TASK_ERROR);
  endtask

  virtual function bit has_do_available();
    ovm_report_error("has_do_available", `SEQ_ITEM_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function void put_response(input T2 t);
    ovm_report_error("put_response", `SEQ_ITEM_FUNCTION_ERROR);
  endfunction

  // tlm_blocking_slave_if
  virtual task get(output T1 t);
    ovm_report_error("get", `SEQ_ITEM_TASK_ERROR);
  endtask

  virtual task peek(output T1 t);
    ovm_report_error("peek", `SEQ_ITEM_TASK_ERROR);
  endtask

  virtual task put(input T2 t);
    ovm_report_error("put", `SEQ_ITEM_TASK_ERROR);
  endtask

endclass
