// $Id:  //dvt/vtech/dev/main/ovm/src/tlm/tlm_fifo_base.svh#5 $
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

`define TLM_FIFO_TASK_ERROR "fifo channel task not implemented"
`define TLM_FIFO_FUNCTION_ERROR "fifo channel function not implemented"

//----------------------------------------------------------------------
// CLASS tlm_event
//----------------------------------------------------------------------
class tlm_event;
  event trigger;
endclass

//----------------------------------------------------------------------
// CLASS tlm_fifo_base
//----------------------------------------------------------------------
virtual class tlm_fifo_base #(type T = int) extends ovm_component;

  typedef tlm_fifo_base #(T) this_type;
  
  ovm_put_imp      #(T, this_type) blocking_put_export;
  ovm_put_imp      #(T, this_type) nonblocking_put_export;
  ovm_put_imp      #(T, this_type) put_export;
  
  ovm_get_peek_imp #(T, this_type) blocking_get_export;
  ovm_get_peek_imp #(T, this_type) nonblocking_get_export;
  ovm_get_peek_imp #(T, this_type) get_export;
  
  ovm_get_peek_imp #(T, this_type) blocking_peek_export;
  ovm_get_peek_imp #(T, this_type) nonblocking_peek_export;
  ovm_get_peek_imp #(T, this_type) peek_export;
  
  ovm_get_peek_imp #(T, this_type) blocking_get_peek_export;
  ovm_get_peek_imp #(T, this_type) nonblocking_get_peek_export;
  ovm_get_peek_imp #(T, this_type) get_peek_export;  

  ovm_analysis_port #(T) put_ap, get_ap;

  //--------------------------------------------------------------------
  // constructor (new)
  //--------------------------------------------------------------------
  function new(string name, ovm_component parent = null);
    super.new(name, parent);

    put_export = new("put_export", this);
    blocking_put_export     = put_export;
    nonblocking_put_export  = put_export;

    get_peek_export = new("get_peek_export", this);
    blocking_get_peek_export    = get_peek_export;
    nonblocking_get_peek_export = get_peek_export;
    blocking_get_export         = get_peek_export;
    nonblocking_get_export      = get_peek_export;
    get_export                  = get_peek_export;
    blocking_peek_export        = get_peek_export;
    nonblocking_peek_export     = get_peek_export;
    peek_export                 = get_peek_export;

    put_ap = new("put_ap", this);
    get_ap = new("get_ap", this);
    
  endfunction

  virtual function void flush();
    ovm_report_error("flush", `TLM_FIFO_FUNCTION_ERROR);
  endfunction
  
  virtual function int used();
    ovm_report_error("used", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function int size();
    ovm_report_error("size", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual task put(T t);
    ovm_report_error("put", `TLM_FIFO_TASK_ERROR);
  endtask

  virtual task get(output T t);
    ovm_report_error("get", `TLM_FIFO_TASK_ERROR);
  endtask

  virtual task peek(output T t);
    ovm_report_error("peek", `TLM_FIFO_TASK_ERROR);
  endtask
  
  virtual function bit try_put(T t);
    ovm_report_error("try_put", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit try_get(output T t);
    ovm_report_error("try_get", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit try_peek(output T t);
    ovm_report_error("try_peek", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction
  
  virtual function bit can_put();
    ovm_report_error("can_put", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_get();
    ovm_report_error("can_get", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_peek();
    ovm_report_error("can_peek", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function tlm_event ok_to_put();
    ovm_report_error("ok_to_put", `TLM_FIFO_FUNCTION_ERROR);
    return null;
  endfunction

  virtual function tlm_event ok_to_get();
    ovm_report_error("ok_to_get", `TLM_FIFO_FUNCTION_ERROR);
    return null;
  endfunction

  virtual function tlm_event ok_to_peek();
    ovm_report_error("ok_to_peek", `TLM_FIFO_FUNCTION_ERROR);
    return null;
  endfunction

  virtual function bit is_empty();
    ovm_report_error("is_empty", `TLM_FIFO_FUNCTION_ERROR);
    return 0;
  endfunction

endclass
