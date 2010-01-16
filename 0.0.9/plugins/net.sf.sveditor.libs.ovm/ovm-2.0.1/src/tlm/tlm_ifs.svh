// $Id: //dvt/vtech/dev/main/ovm/src/tlm/tlm_ifs.svh#7 $
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
//
// TLM Interfaces
//
//----------------------------------------------------------------------
//
// The unidirectional TLM interfaces are divided into put, get and peek
// interfaces, and blocking, nonblocking and combined interfaces.
// 
// A blocking call always succeeds, but may need to consume time to do
// so. As a result, these methods must be tasks.
//
// A nonblocking call may not succeed, but consumes no time. As a result,
// these methods are functions.
//
// The difference between get and peek is that get consumes the data
// while peek does not. So successive calls to peek with no calls get
// or try_get are guaranteed to return the same value.
//
// The transport interface is a bidirectional blocking interface used
// when the request and response are tightly coupled in a one to one
// relationship.
//----------------------------------------------------------------------

`define TASK_ERROR "TLM interface task not implemented"
`define FUNCTION_ERROR "TLM interface function not implemented"

virtual class tlm_if_base #(type T1=int, type T2=int);

  virtual task put( input T1 t );
    ovm_report_error("put", `TASK_ERROR);
  endtask

  virtual task get( output T2 t );
    ovm_report_error("get", `TASK_ERROR);
  endtask

  virtual task peek( output T2 t );
    ovm_report_error("peek", `TASK_ERROR);
  endtask

  virtual function bit try_put( input T1 t );
    ovm_report_error("try_put", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_put();
    ovm_report_error("can_put", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit try_get( output T2 t );
    ovm_report_error("try_get", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_get();
    ovm_report_error("can_get", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit try_peek( output T2 t );
    ovm_report_error("try_peek", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function bit can_peek();
    ovm_report_error("can_ppeek", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual task transport( input T1 req , output T2 rsp );
    ovm_report_error("transport", `TASK_ERROR);
  endtask

  virtual function bit nb_transport(input T1 req, output T2 rsp);
    ovm_report_error("nb_transport", `FUNCTION_ERROR);
    return 0;
  endfunction

  virtual function void write( input T1 t );
    ovm_report_error("write", `FUNCTION_ERROR);
  endfunction

endclass

