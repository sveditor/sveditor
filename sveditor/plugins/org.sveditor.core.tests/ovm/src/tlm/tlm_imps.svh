// $Id: tlm_imps.svh,v 1.12 2009/10/30 15:29:22 jlrose Exp $
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

`ifndef TLM_IMPS_SVH
`define TLM_IMPS_SVH

//
// These IMP macros define implementations of the ovm_*_port, ovm_*_export,
// and ovm_*_imp ports.
//


//---------------------------------------------------------------
// Macros for implementations of OVM ports and exports

/*
`define BLOCKING_PUT_IMP(imp, TYPE, arg) \
  task put (TYPE arg); \
    if (m_imp_list.size()) == 0) begin \
      ovm_report_error("Port Not Bound","Blocking put to unbound port will wait forever.", OVM_NONE);
      @imp;
    end
    if (bcast_mode) begin \
      if (m_imp_list.size()) > 1) \
        fork
          begin
            foreach (m_imp_list[index]) \
              fork \
                automatic int i = index; \
                begin m_imp_list[i].put(arg); end \
              join_none \
            wait fork; \
          end \
        join \
      else \
        m_imp_list[0].put(arg); \
    end \
    else  \
      if (imp != null) \
        imp.put(arg); \
  endtask \

`define NONBLOCKING_PUT_IMP(imp, TYPE, arg) \
  function bit try_put(input TYPE arg); \
    if (bcast_mode) begin \
      if (!can_put()) \
        return 0; \
      foreach (m_imp_list[index]) \
        void'(m_imp_list[index].try_put(arg)); \
      return 1; \
    end  \
    if (imp != null) \
      return imp.try_put(arg)); \
    return 0; \
  endfunction \
  \
  function bit can_put(); \
    if (bcast_mode) begin \
      if (m_imp_list.size()) begin \
        foreach (m_imp_list[index]) begin \
          if (!m_imp_list[index].can_put() \
            return 0; \
        end \
        return 1; \
      end \
      return 0; \
    end \
    if (imp != null) \
      return imp.can_put(); \
    return 0; \
  endfunction

*/

//-----------------------------------------------------------------------
// TLM imp implementations

`define BLOCKING_PUT_IMP(imp, TYPE, arg) \
  task put (TYPE arg); \
    imp.put(arg); \
  endtask

`define NONBLOCKING_PUT_IMP(imp, TYPE, arg) \
  function bit try_put (TYPE arg); \
    return imp.try_put(arg); \
  endfunction \
  function bit can_put(); \
    return imp.can_put(); \
  endfunction

`define BLOCKING_GET_IMP(imp, TYPE, arg) \
  task get (output TYPE arg); \
    imp.get(arg); \
  endtask

`define NONBLOCKING_GET_IMP(imp, TYPE, arg) \
  function bit try_get (output TYPE arg); \
    return imp.try_get(arg); \
  endfunction \
  function bit can_get(); \
    return imp.can_get(); \
  endfunction

`define BLOCKING_PEEK_IMP(imp, TYPE, arg) \
  task peek (output TYPE arg); \
    imp.peek(arg); \
  endtask

`define NONBLOCKING_PEEK_IMP(imp, TYPE, arg) \
  function bit try_peek (output TYPE arg); \
    return imp.try_peek(arg); \
  endfunction \
  function bit can_peek(); \
    return imp.can_peek(); \
  endfunction

`define BLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  task transport (REQ req_arg, output RSP rsp_arg); \
    imp.transport(req_arg, rsp_arg); \
  endtask

`define NONBLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  function bit nb_transport (REQ req_arg, output RSP rsp_arg); \
    return imp.nb_transport(req_arg, rsp_arg); \
  endfunction

`define PUT_IMP(imp, TYPE, arg) \
  `BLOCKING_PUT_IMP(imp, TYPE, arg) \
  `NONBLOCKING_PUT_IMP(imp, TYPE, arg)

`define GET_IMP(imp, TYPE, arg) \
  `BLOCKING_GET_IMP(imp, TYPE, arg) \
  `NONBLOCKING_GET_IMP(imp, TYPE, arg)

`define PEEK_IMP(imp, TYPE, arg) \
  `BLOCKING_PEEK_IMP(imp, TYPE, arg) \
  `NONBLOCKING_PEEK_IMP(imp, TYPE, arg)

`define BLOCKING_GET_PEEK_IMP(imp, TYPE, arg) \
  `BLOCKING_GET_IMP(imp, TYPE, arg) \
  `BLOCKING_PEEK_IMP(imp, TYPE, arg)

`define NONBLOCKING_GET_PEEK_IMP(imp, TYPE, arg) \
  `NONBLOCKING_GET_IMP(imp, TYPE, arg) \
  `NONBLOCKING_PEEK_IMP(imp, TYPE, arg)

`define GET_PEEK_IMP(imp, TYPE, arg) \
  `BLOCKING_GET_PEEK_IMP(imp, TYPE, arg) \
  `NONBLOCKING_GET_PEEK_IMP(imp, TYPE, arg)

`define TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  `BLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  `NONBLOCKING_TRANSPORT_IMP(imp, REQ, RSP, req_arg, rsp_arg)



`define TLM_GET_TYPE_NAME(NAME) \
  virtual function string get_type_name(); \
    return NAME; \
  endfunction

`define OVM_PORT_COMMON(MASK,TYPE_NAME) \
  function new (string name, ovm_component parent, \
                int min_size=1, int max_size=1); \
    super.new (name, parent, OVM_PORT, min_size, max_size); \
    m_if_mask = MASK; \
  endfunction \
  `TLM_GET_TYPE_NAME(TYPE_NAME)

`define OVM_SEQ_PORT(MASK,TYPE_NAME) \
  function new (string name, ovm_component parent, \
                int min_size=0, int max_size=1); \
    super.new (name, parent, OVM_PORT, min_size, max_size); \
    m_if_mask = MASK; \
  endfunction \
  `TLM_GET_TYPE_NAME(TYPE_NAME)
  
`define OVM_EXPORT_COMMON(MASK,TYPE_NAME) \
  function new (string name, ovm_component parent, \
                int min_size=1, int max_size=1); \
    super.new (name, parent, OVM_EXPORT, min_size, max_size); \
    m_if_mask = MASK; \
  endfunction \
  `TLM_GET_TYPE_NAME(TYPE_NAME)
  
`define OVM_IMP_COMMON(MASK,TYPE_NAME,IMP) \
  local IMP m_imp; \
  function new (string name, IMP imp); \
    super.new (name, imp, OVM_IMPLEMENTATION, 1, 1); \
    m_imp = imp; \
    m_if_mask = MASK; \
  endfunction \
  `TLM_GET_TYPE_NAME(TYPE_NAME)

`define OVM_MS_IMP_COMMON(MASK,TYPE_NAME) \
  local this_req_type m_req_imp; \
  local this_rsp_type m_rsp_imp; \
  function new (string name, this_imp_type imp, \
                this_req_type req_imp = null, this_rsp_type rsp_imp = null); \
    super.new (name, imp, OVM_IMPLEMENTATION, 1, 1); \
    if(req_imp==null) $cast(req_imp, imp); \
    if(rsp_imp==null) $cast(rsp_imp, imp); \
    m_req_imp = req_imp; \
    m_rsp_imp = rsp_imp; \
    m_if_mask = MASK; \
  endfunction  \
  `TLM_GET_TYPE_NAME(TYPE_NAME)

`endif
