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

// The following macros: ovm_IF_imp_decl all users to create implemenation
// classes which a predefined tlm interface but add a suffix to the 
// implementation methods. This allows multiple interfaces of the same type
// to be implemented in the same scope.
//
// For example:
//
// `ovm_blocking_put_imp_decl(_1)
// `ovm_blocking_put_imp_decl(_2)
// class my_put_imp#(type T=int) extends ovm_component;
//    ovm_blocking_put_imp_1#(T) export1;
//    ovm_blocking_put_imp_2#(T) export2;
//    ...
//    function void put_1 (input T t);
//      //puts comming into export1
//      ...
//    endfunction
//    function void put_2(input T t);
//      //puts comming into export2
//      ...
//    endfunction
// endclass

// Note that the default, unsuffixed, implementations live in the file
// tlm/ovm_imps.sv.

`define ovm_blocking_put_imp_decl(SFX) \
class ovm_blocking_put_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_PUT_MASK,`"ovm_blocking_put_imp``SFX`",IMP) \
  `BLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_nonblocking_put_imp_decl(SFX) \
class ovm_nonblocking_put_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PUT_MASK,`"ovm_nonblocking_put_imp``SFX`",IMP) \
  `NONBLOCKING_PUT_IMP_SFX( SFX, m_imp, T, t) \
endclass

`define ovm_put_imp_decl(SFX) \
class ovm_put_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_PUT_MASK,`"ovm_put_imp``SFX`",IMP) \
  `BLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_blocking_get_imp_decl(SFX) \
class ovm_blocking_get_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_MASK,`"ovm_blocking_get_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_nonblocking_get_imp_decl(SFX) \
class ovm_nonblocking_get_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_MASK,`"ovm_nonblocking_get_imp``SFX`",IMP) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_get_imp_decl(SFX) \
class ovm_get_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_GET_MASK,`"ovm_get_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_blocking_peek_imp_decl(SFX) \
class ovm_blocking_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_PEEK_MASK,`"ovm_blocking_peek_imp``SFX`",IMP) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass 

`define ovm_nonblocking_peek_imp_decl(SFX) \
class ovm_nonblocking_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_PEEK_MASK,`"ovm_nonblocking_peek_imp``SFX`",IMP) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_peek_imp_decl(SFX) \
class ovm_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_PEEK_MASK,`"ovm_peek_imp``SFX`",IMP) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass


`define ovm_blocking_get_peek_imp_decl(SFX) \
class ovm_blocking_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_GET_PEEK_MASK,`"ovm_blocking_get_peek_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_nonblocking_get_peek_imp_decl(SFX) \
class ovm_nonblocking_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_GET_PEEK_MASK,`"ovm_nonblocking_get_peek_imp``SFX`",IMP) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_get_peek_imp_decl(SFX) \
class ovm_get_peek_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_GET_PEEK_MASK,`"ovm_get_peek_imp``SFX`",IMP) \
  `BLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_imp, T, t) \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_imp, T, t) \
endclass

`define ovm_blocking_master_imp_decl(SFX) \
class ovm_blocking_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                     type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_MASTER_MASK,`"ovm_blocking_master_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
endclass

`define ovm_nonblocking_master_imp_decl(SFX) \
class ovm_nonblocking_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                   type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_MASTER_MASK,`"ovm_nonblocking_master_imp``SFX`") \
  \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
endclass

`define ovm_master_imp_decl(SFX) \
class ovm_master_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                            type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_MASTER_MASK,`"ovm_master_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
endclass

`define ovm_blocking_slave_imp_decl(SFX) \
class ovm_blocking_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                    type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_BLOCKING_SLAVE_MASK,`"ovm_blocking_slave_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
endclass

`define ovm_nonblocking_slave_imp_decl(SFX) \
class ovm_nonblocking_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                                       type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_NONBLOCKING_SLAVE_MASK,`"ovm_nonblocking_slave_imp``SFX`") \
  \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
endclass

`define ovm_slave_imp_decl(SFX) \
class ovm_slave_imp``SFX #(type REQ=int, type RSP=int, type IMP=int, \
                           type REQ_IMP=IMP, type RSP_IMP=IMP) \
  extends ovm_port_base #(tlm_if_base #(RSP, REQ)); \
  typedef IMP     this_imp_type; \
  typedef REQ_IMP this_req_type; \
  typedef RSP_IMP this_rsp_type; \
  `OVM_MS_IMP_COMMON(`TLM_SLAVE_MASK,`"ovm_slave_imp``SFX`") \
  \
  `BLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  `NONBLOCKING_PUT_IMP_SFX(SFX, m_rsp_imp, RSP, t) // rsp \
  \
  `BLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `BLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_GET_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  `NONBLOCKING_PEEK_IMP_SFX(SFX, m_req_imp, REQ, t) // req \
  \
endclass

`define ovm_blocking_transport_imp_decl(SFX) \
class ovm_blocking_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  `OVM_IMP_COMMON(`TLM_BLOCKING_TRANSPORT_MASK,`"ovm_blocking_transport_imp``SFX`",IMP) \
  `BLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass

`define ovm_non_blocking_transport_imp_decl(SFX) \
  ovm_nonblocking_transport_imp_decl(SFX)

`define ovm_nonblocking_transport_imp_decl(SFX) \
class ovm_nonblocking_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  `OVM_IMP_COMMON(`TLM_NONBLOCKING_TRANSPORT_MASK,`"ovm_nonblocking_transport_imp``SFX`",IMP) \
  `NONBLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass

`define ovm_transport_imp_decl(SFX) \
class ovm_transport_imp``SFX #(type REQ=int, type RSP=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(REQ, RSP)); \
  `OVM_IMP_COMMON(`TLM_TRANSPORT_MASK,`"ovm_transport_imp``SFX`",IMP) \
  `BLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
  `NONBLOCKING_TRANSPORT_IMP_SFX(SFX, m_imp, REQ, RSP, req, rsp) \
endclass

`define ovm_analysis_imp_decl(SFX) \
class ovm_analysis_imp``SFX #(type T=int, type IMP=int) \
  extends ovm_port_base #(tlm_if_base #(T,T)); \
  `OVM_IMP_COMMON(`TLM_ANALYSIS_MASK,`"ovm_analysis_imp``SFX`",IMP) \
  function void write( input T t); \
    m_imp.write``SFX( t); \
  endfunction \
  \
endclass


// These imps are used in ovm_*_port, ovm_*_export and ovm_*_imp, using suffixes
//

`define BLOCKING_PUT_IMP_SFX(SFX, imp, TYPE, arg) \
  task put( input TYPE arg); imp.put``SFX( arg); endtask

`define BLOCKING_GET_IMP_SFX(SFX, imp, TYPE, arg) \
  task get( output TYPE arg); imp.get``SFX( arg); endtask

`define BLOCKING_PEEK_IMP_SFX(SFX, imp, TYPE, arg) \
  task peek( output TYPE arg);imp.peek``SFX( arg); endtask

`define NONBLOCKING_PUT_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_put( input TYPE arg); \
    if( !imp.try_put``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_put(); return imp.can_put``SFX(); endfunction

`define NONBLOCKING_GET_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_get( output TYPE arg); \
    if( !imp.try_get``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_get(); return imp.can_get``SFX(); endfunction

`define NONBLOCKING_PEEK_IMP_SFX(SFX, imp, TYPE, arg) \
  function bit try_peek( output TYPE arg); \
    if( !imp.try_peek``SFX( arg)) return 0; \
    return 1; \
  endfunction \
  function bit can_peek(); return imp.can_peek``SFX(); endfunction

`define BLOCKING_TRANSPORT_IMP_SFX(SFX, imp, REQ, RSP, req_arg, rsp_arg) \
  task transport( input REQ req_arg, output RSP rsp_arg); \
    imp.transport``SFX(req_arg, rsp_arg); \
  endtask

`define NONBLOCKING_TRANSPORT_IMP_SFX(SFX, imp, REQ, RSP, req_arg, rsp_arg) \
  function bit nb_transport( input REQ req_arg, output RSP rsp_arg); \
    if(imp) return imp.nb_transport``SFX(req_arg, rsp_arg); \
  endfunction

//----------------------------------------------------------------------
// imp definitions
//----------------------------------------------------------------------
`define SEQ_ITEM_PULL_IMP(imp, REQ, RSP, req_arg, rsp_arg) \
  task get_next_item(output REQ req_arg); imp.get_next_item(req_arg); endtask \
  task try_next_item(output REQ req_arg); imp.try_next_item(req_arg); endtask \
  function void item_done(input RSP rsp_arg = null); imp.item_done(rsp_arg); endfunction \
  task wait_for_sequences(); imp.wait_for_sequences(); endtask \
  function bit has_do_available(); return imp.has_do_available(); endfunction \
  function void put_response(input RSP rsp_arg); imp.put_response(rsp_arg); endfunction \
  task get(output REQ req_arg); imp.get(req_arg); endtask \
  task peek(output REQ req_arg); imp.peek(req_arg); endtask \
  task put(input RSP rsp_arg); imp.put(rsp_arg); endtask

// primitive interfaces
`define TLM_BLOCKING_PUT_MASK          (1<<0)
`define TLM_BLOCKING_GET_MASK          (1<<1)
`define TLM_BLOCKING_PEEK_MASK         (1<<2)
`define TLM_BLOCKING_TRANSPORT_MASK    (1<<3)

`define TLM_NONBLOCKING_PUT_MASK       (1<<4)
`define TLM_NONBLOCKING_GET_MASK       (1<<5)
`define TLM_NONBLOCKING_PEEK_MASK      (1<<6)
`define TLM_NONBLOCKING_TRANSPORT_MASK (1<<7)

`define TLM_ANALYSIS_MASK              (1<<8)

`define TLM_MASTER_BIT_MASK            (1<<9)
`define TLM_SLAVE_BIT_MASK             (1<<10)
// combination interfaces
`define TLM_PUT_MASK                  (`TLM_BLOCKING_PUT_MASK    | `TLM_NONBLOCKING_PUT_MASK)
`define TLM_GET_MASK                  (`TLM_BLOCKING_GET_MASK    | `TLM_NONBLOCKING_GET_MASK)
`define TLM_PEEK_MASK                 (`TLM_BLOCKING_PEEK_MASK   | `TLM_NONBLOCKING_PEEK_MASK)

`define TLM_BLOCKING_GET_PEEK_MASK    (`TLM_BLOCKING_GET_MASK    | `TLM_BLOCKING_PEEK_MASK)
`define TLM_BLOCKING_MASTER_MASK      (`TLM_BLOCKING_PUT_MASK       | `TLM_BLOCKING_GET_MASK | `TLM_BLOCKING_PEEK_MASK | `TLM_MASTER_BIT_MASK)
`define TLM_BLOCKING_SLAVE_MASK       (`TLM_BLOCKING_PUT_MASK       | `TLM_BLOCKING_GET_MASK | `TLM_BLOCKING_PEEK_MASK | `TLM_SLAVE_BIT_MASK)

`define TLM_NONBLOCKING_GET_PEEK_MASK (`TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK)
`define TLM_NONBLOCKING_MASTER_MASK   (`TLM_NONBLOCKING_PUT_MASK    | `TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK | `TLM_MASTER_BIT_MASK)
`define TLM_NONBLOCKING_SLAVE_MASK    (`TLM_NONBLOCKING_PUT_MASK    | `TLM_NONBLOCKING_GET_MASK | `TLM_NONBLOCKING_PEEK_MASK | `TLM_SLAVE_BIT_MASK)

`define TLM_GET_PEEK_MASK             (`TLM_GET_MASK | `TLM_PEEK_MASK)
`define TLM_MASTER_MASK               (`TLM_BLOCKING_MASTER_MASK    | `TLM_NONBLOCKING_MASTER_MASK)
`define TLM_SLAVE_MASK                (`TLM_BLOCKING_SLAVE_MASK    | `TLM_NONBLOCKING_SLAVE_MASK)
`define TLM_TRANSPORT_MASK            (`TLM_BLOCKING_TRANSPORT_MASK | `TLM_NONBLOCKING_TRANSPORT_MASK)

`define SEQ_ITEM_GET_NEXT_ITEM_MASK       (1<<0)
`define SEQ_ITEM_TRY_NEXT_ITEM_MASK       (1<<1)
`define SEQ_ITEM_ITEM_DONE_MASK           (1<<2)
`define SEQ_ITEM_HAS_DO_AVAILABLE_MASK    (1<<3)
`define SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK  (1<<4)
`define SEQ_ITEM_PUT_RESPONSE_MASK        (1<<5)
`define SEQ_ITEM_PUT_MASK                 (1<<6)
`define SEQ_ITEM_GET_MASK                 (1<<7)
`define SEQ_ITEM_PEEK_MASK                (1<<8)

`define SEQ_ITEM_PULL_MASK  (`SEQ_ITEM_GET_NEXT_ITEM_MASK | `SEQ_ITEM_TRY_NEXT_ITEM_MASK | \
                        `SEQ_ITEM_ITEM_DONE_MASK | `SEQ_ITEM_HAS_DO_AVAILABLE_MASK |  \
                        `SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK | `SEQ_ITEM_PUT_RESPONSE_MASK | \
                        `SEQ_ITEM_PUT_MASK | `SEQ_ITEM_GET_MASK | `SEQ_ITEM_PEEK_MASK)

`define SEQ_ITEM_UNI_PULL_MASK (`SEQ_ITEM_GET_NEXT_ITEM_MASK | `SEQ_ITEM_TRY_NEXT_ITEM_MASK | \
                           `SEQ_ITEM_ITEM_DONE_MASK | `SEQ_ITEM_HAS_DO_AVAILABLE_MASK | \
                           `SEQ_ITEM_WAIT_FOR_SEQUENCES_MASK | `SEQ_ITEM_GET_MASK | \
                           `SEQ_ITEM_PEEK_MASK)

`define SEQ_ITEM_PUSH_MASK  (`SEQ_ITEM_PUT_MASK)

`include "tlm/tlm_imps.svh"
