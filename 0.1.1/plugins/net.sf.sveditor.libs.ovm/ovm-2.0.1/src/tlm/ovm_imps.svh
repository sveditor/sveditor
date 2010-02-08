// $Id: //dvt/vtech/dev/main/ovm/src/tlm/ovm_imps.svh#8 $
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

class ovm_blocking_put_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_PUT_MASK,"ovm_blocking_put_imp",IMP)
  `BLOCKING_PUT_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_put_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PUT_MASK,"ovm_nonblocking_put_imp",IMP)
  `NONBLOCKING_PUT_IMP (m_imp, T, t)
endclass

class ovm_put_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_PUT_MASK,"ovm_put_imp",IMP)
  `PUT_IMP (m_imp, T, t)
endclass

class ovm_blocking_get_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_MASK,"ovm_blocking_get_imp",IMP)
  `BLOCKING_GET_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_get_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_MASK,"ovm_nonblocking_get_imp",IMP)
  `NONBLOCKING_GET_IMP (m_imp, T, t)
endclass

class ovm_get_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_GET_MASK,"ovm_get_imp",IMP)
  `GET_IMP (m_imp, T, t)
endclass

class ovm_blocking_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_PEEK_MASK,"ovm_blocking_peek_imp",IMP)
  `BLOCKING_PEEK_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PEEK_MASK,"ovm_nonblocking_peek_imp",IMP)
  `NONBLOCKING_PEEK_IMP (m_imp, T, t)
endclass

class ovm_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_PEEK_MASK,"ovm_peek_imp",IMP)
  `PEEK_IMP (m_imp, T, t)
endclass

class ovm_blocking_get_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_PEEK_MASK,"ovm_blocking_get_peek_imp",IMP)
  `BLOCKING_GET_PEEK_IMP (m_imp, T, t)
endclass

class ovm_nonblocking_get_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_PEEK_MASK,"ovm_nonblocking_get_peek_imp",IMP)
  `NONBLOCKING_GET_PEEK_IMP (m_imp, T, t)
endclass

class ovm_get_peek_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_GET_PEEK_MASK,"ovm_get_peek_imp",IMP)
  `GET_PEEK_IMP (m_imp, T, t)
endclass

//
// All the master and slave imps have two modes of operation.
//
// The first could be described as normal but unusual. In other words
// it fits the pattern of the other imps but in practise is unusual.
//
// This is when there is a single class  (type IMP) that implements the
// entire interface, and imp -= req_imp == rsp_imp.
//
// The reason this is unusual is that we do not have C++ style name
// mangling in SV, so such a channel will not be able to implement both
// a master and a slave interface, even if REQ != RSP
//
// The abnormal but more usual pattern is where two siblings implement
// the request and response methods. In this case req_imp and rsp_imp
// are children of imp, as is the implementation itself.
//
// This second pattern is used in tlm_req_rsp_channel, for example.
//

class ovm_blocking_master_imp #(type REQ=int, type RSP=int, type IMP=int,
                                type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_MASTER_MASK,"ovm_blocking_master_imp")
  `BLOCKING_PUT_IMP (m_req_imp, REQ, t)
  `BLOCKING_GET_PEEK_IMP (m_rsp_imp, RSP, t)
endclass

class ovm_nonblocking_master_imp #(type REQ=int, type RSP=int, type IMP=int,
                                   type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_MASTER_MASK,"ovm_nonblocking_master_imp")
  `NONBLOCKING_PUT_IMP (m_req_imp, REQ, t)
  `NONBLOCKING_GET_PEEK_IMP (m_rsp_imp, RSP, t)
endclass

class ovm_master_imp #(type REQ=int, type RSP=int, type IMP=int,
                       type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_MASTER_MASK,"ovm_master_imp")
  `PUT_IMP (m_req_imp, REQ, t)
  `GET_PEEK_IMP (m_rsp_imp, RSP, t)
endclass

class ovm_blocking_slave_imp #(type REQ=int, type RSP=int, type IMP=int,
                               type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_SLAVE_MASK,"ovm_blocking_slave_imp")
  `BLOCKING_PUT_IMP (m_rsp_imp, RSP, t)
  `BLOCKING_GET_PEEK_IMP (m_req_imp, REQ, t)
endclass

class ovm_nonblocking_slave_imp #(type REQ=int, type RSP=int, type IMP=int,
                                  type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_SLAVE_MASK,"ovm_nonblocking_slave_imp")
  `NONBLOCKING_PUT_IMP (m_rsp_imp, RSP, t)
  `NONBLOCKING_GET_PEEK_IMP (m_req_imp, REQ, t)
endclass

class ovm_slave_imp #(type REQ=int, type RSP=int, type IMP=int,
                      type REQ_IMP=IMP, type RSP_IMP=IMP)
  extends ovm_port_base #(tlm_if_base #(RSP, REQ));
  typedef IMP     this_imp_type;
  typedef REQ_IMP this_req_type;
  typedef RSP_IMP this_rsp_type;
  `OVM_MS_IMP_COMMON(`TLM_SLAVE_MASK,"ovm_slave_imp")
  `PUT_IMP (m_rsp_imp, RSP, t)
  `GET_PEEK_IMP (m_req_imp, REQ, t)
endclass

class ovm_blocking_transport_imp #(type REQ=int, type RSP=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`TLM_BLOCKING_TRANSPORT_MASK,"ovm_blocking_transport_imp",IMP)
  `BLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
endclass

class ovm_nonblocking_transport_imp #(type REQ=int, type RSP=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_TRANSPORT_MASK,"ovm_nonblocking_transport_imp",IMP)
  `NONBLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
endclass

class ovm_transport_imp #(type REQ=int, type RSP=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(REQ, RSP));
  `OVM_IMP_COMMON(`TLM_TRANSPORT_MASK,"ovm_transport_imp",IMP)
  `BLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
  `NONBLOCKING_TRANSPORT_IMP (m_imp, REQ, RSP, req, rsp)
endclass

class ovm_analysis_imp #(type T=int, type IMP=int)
  extends ovm_port_base #(tlm_if_base #(T,T));
  `OVM_IMP_COMMON(`TLM_ANALYSIS_MASK,"ovm_analysis_imp",IMP)
  function void write (input T t);
    m_imp.write (t);
  endfunction
endclass
