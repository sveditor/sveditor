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

`define ovm_register_sequence(TYPE_NAME, SEQUENCER) \
  static bit is_registered_with_sequencer = SEQUENCER``::add_typewide_sequence(`"TYPE_NAME`");

`define ovm_declare_p_sequencer(SEQUENCER) \
  SEQUENCER p_sequencer;\
  virtual function void m_set_p_sequencer();\
    super.m_set_p_sequencer(); \
    assert($cast(p_sequencer, m_sequencer)) else \
        ovm_report_fatal("DCLPSQ", \
        $psprintf("%m Error casting p_sequencer, please verify that this sequence/sequence item is intended to execute on this type of sequencer")); \
  endfunction  

`define ovm_sequence_utils_begin(TYPE_NAME, SEQUENCER) \
  `ovm_register_sequence(TYPE_NAME, SEQUENCER) \
  `ovm_declare_p_sequencer(SEQUENCER) \
  `ovm_object_utils_begin(TYPE_NAME)

`define ovm_sequence_utils_end \
  `ovm_object_utils_end

`define ovm_sequence_utils(TYPE_NAME, SEQUENCER) \
  `ovm_sequence_utils_begin(TYPE_NAME,SEQUENCER) \
  `ovm_sequence_utils_end

//-----------------------------------------------------------------------------
//
// MACRO: ovm_package
//
// Use `ovm_package to define the SV package and to create a bogus type to help 
// automate triggering the static initializers of the package.
// Use ovm_end_package to endpackage.
//-----------------------------------------------------------------------------

`define ovm_package(PKG) \
  package PKG; \
  class ovm_bogus_class extends ovm::ovm_sequence;\
  endclass

`define ovm_end_package \
   endpackage


//-----------------------------------------------------------------------------
//
// MACRO: ovm_sequence_library_package
//
// Use `ovm_sequence_library_package to automate triggering of packages static 
// initializers.  ovm_package creates a bogus type which gets referred to by 
// ovm_sequence_library_package to make a package-based variable of the bogus
// type.
//-----------------------------------------------------------------------------

`define ovm_sequence_library_package(PKG_NAME) \
  import PKG_NAME``::*; \
  PKG_NAME``::ovm_bogus_class M_``PKG_NAME``ovm_bogus_class


//------------------------------------------------------------------------------
//
// MACRO: ovm_create
//
//------------------------------------------------------------------------------

// This macro takes as an argument a ovm_sequence_item variable or object.  
// Memory is allocated using the factory and is assigned to the macro arguement.

`define ovm_create(OVM_SEQUENCE_ITEM) \
  begin \
  ovm_object_wrapper w_; w_ = OVM_SEQUENCE_ITEM.get_type(); \
  $cast(OVM_SEQUENCE_ITEM , create_item(w_, m_sequencer, `"OVM_SEQUENCE_ITEM`"));\
  end\

//------------------------------------------------------------------------------
//
// MACRO: ovm_do
//
//------------------------------------------------------------------------------

// This macro takes as an argument a ovm_sequence_item variable or object.  
// Memory is allocated using the factory and is assigned to the macro arguement.
// ovm_sequence_item's are randomized using late-randomization.
// See the "ovm_do item Flow in Pull Mode" and the "ovm_do Subsequence Flow" 
// diagrams for further details.

`define ovm_do(OVM_SEQUENCE_ITEM) \
  begin \
  OVM_SEQUENCE_ITEM = new(""); \
  `ovm_create(OVM_SEQUENCE_ITEM) \
  start_item(OVM_SEQUENCE_ITEM); \
  assert(OVM_SEQUENCE_ITEM.randomize()) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM); \
  end

`define ovm_do_pri(OVM_SEQUENCE_ITEM, PRIORITY) \
  begin \
  `ovm_create(OVM_SEQUENCE_ITEM) \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  assert(OVM_SEQUENCE_ITEM.randomize()) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  end

//------------------------------------------------------------------------------
//
// MACRO: ovm_do_with
//
//------------------------------------------------------------------------------

// Similar to ovm_do with in-line constraints provided as a 2nd argument.
// The user must supply brackets around the constraints.

`define ovm_do_with(OVM_SEQUENCE_ITEM, CONSTRAINTS) \
  begin \
  OVM_SEQUENCE_ITEM = new(""); \
  `ovm_create(OVM_SEQUENCE_ITEM) \
  start_item(OVM_SEQUENCE_ITEM);\
  assert(OVM_SEQUENCE_ITEM.randomize() with CONSTRAINTS ) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do_with action"); \
  end\
  finish_item(OVM_SEQUENCE_ITEM);\
  end

`define ovm_do_pri_with(OVM_SEQUENCE_ITEM, PRIORITY, CONSTRAINTS) \
begin \
  OVM_SEQUENCE_ITEM = new(""); \
  `ovm_create(OVM_SEQUENCE_ITEM) \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  assert(OVM_SEQUENCE_ITEM.randomize() with CONSTRAINTS ) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do_with action"); \
  end\
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  end

//------------------------------------------------------------------------------
//
// MACRO: ovm_send
//
//------------------------------------------------------------------------------

// Takes as an argument a ovm_sequence_item object (likely created with 
// create_item).  
// Memory is not allocated. 
// Sequence items are sent to the DRIVER with standard processing.


`define ovm_send(OVM_SEQUENCE_ITEM) \
  begin \
  start_item(OVM_SEQUENCE_ITEM); \
  finish_item(OVM_SEQUENCE_ITEM);\
  end\
  
`define ovm_send_pri(OVM_SEQUENCE_ITEM, PRIORITY) \
  begin \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  end\
  

//------------------------------------------------------------------------------
//
// MACRO: ovm_rand_send
//
//------------------------------------------------------------------------------

// Takes as an argument a ovm_sequence_item object (likely created with 
// create_item).  
// Memory is not allocated. 
// Sequence items are sent to the DRIVER with standard processing.
// ovm_sequence_item's are randomized using late-randomization.

`define ovm_rand_send(OVM_SEQUENCE_ITEM) \
  begin \
  start_item(OVM_SEQUENCE_ITEM); \
  assert(OVM_SEQUENCE_ITEM.randomize()) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_rand_send action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM);\
  end\

`define ovm_rand_send_pri(OVM_SEQUENCE_ITEM, PRIORITY) \
  begin \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  assert(OVM_SEQUENCE_ITEM.randomize()) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_rand_send action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  end\


//------------------------------------------------------------------------------
//
// MACRO: ovm_rand_send_with
//
//------------------------------------------------------------------------------

// Similar to ovm_rand_send with in-line constraints provided as a 2nd argument
// The user must supply brackets around the constraints.


`define ovm_rand_send_with(OVM_SEQUENCE_ITEM, CONSTRAINTS) \
  begin \
  start_item(OVM_SEQUENCE_ITEM); \
  assert(OVM_SEQUENCE_ITEM.randomize() with CONSTRAINTS ) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_rand_send_with action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM);\
  end\

`define ovm_rand_send_pri_with(OVM_SEQUENCE_ITEM, PRIORITY, CONSTRAINTS) \
  begin \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  assert(OVM_SEQUENCE_ITEM.randomize() with CONSTRAINTS ) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_rand_send_with action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  end\


`define ovm_declare_sequence_lib \
  protected bit m_set_sequences_called = 1;    \
  static protected string m_static_sequences[$]; \
  static function bit add_typewide_sequence(string type_name); \
    m_static_sequences.push_back(type_name); \
    return 1; \
  endfunction\
  static function bit remove_typewide_sequence(string type_name); \
    for (int i = 0; i < m_static_sequences.size(); i++) begin \
      if (m_static_sequences[i] == type_name) \
        m_static_sequences.delete(i); \
    end \
    return 1;\
  endfunction\
  function void ovm_update_sequence_lib();\
    if(this.m_set_sequences_called) begin \
      set_sequences_queue(m_static_sequences); \
      this.m_set_sequences_called = 0;\
    end\
  endfunction\

`define ovm_update_sequence_lib \
  m_add_builtin_seqs(0); \
  ovm_update_sequence_lib();


`define ovm_update_sequence_lib_and_item(USER_ITEM) \
  factory.set_inst_override_by_type( \
    ovm_sequence_item::get_type(), USER_ITEM::get_type(), \
    {get_full_name(), "*.item"}); \
  m_add_builtin_seqs(1); \
  ovm_update_sequence_lib();

`define ovm_sequencer_utils_begin(TYPE_NAME) \
  `ovm_declare_sequence_lib \
  `ovm_component_utils_begin(TYPE_NAME)

`define ovm_sequencer_param_utils_begin(TYPE_NAME) \
  `ovm_declare_sequence_lib \
  `ovm_component_param_utils_begin(TYPE_NAME)

`define ovm_sequencer_utils_end \
  `ovm_component_utils_end

`define ovm_sequencer_utils(TYPE_NAME) \
  `ovm_sequencer_utils_begin(TYPE_NAME) \
  `ovm_sequencer_utils_end

`define ovm_sequencer_param_utils(TYPE_NAME) \
  `ovm_sequencer_param_utils_begin(TYPE_NAME) \
  `ovm_sequencer_utils_end

//-----------------------------------------------------------------------------
// MACRO: ovm_create_on
// This macro is used by virtual sequences to execute driver sequences
//-----------------------------------------------------------------------------

`define ovm_create_on(OVM_SEQUENCE_ITEM, SEQUENCER_REF) \
  begin \
  ovm_object_wrapper w_; w_ = OVM_SEQUENCE_ITEM.get_type(); \
  $cast(OVM_SEQUENCE_ITEM , create_item(w_, SEQUENCER_REF, `"OVM_SEQUENCE_ITEM`"));\
  end

`define ovm_create_seq(OVM_SEQ, SEQR_CONS_IF) \
  begin \
  `ovm_create_on(OVM_SEQ, SEQR_CONS_IF.consumer_seqr) \
  end

//-----------------------------------------------------------------------------
// MACRO: ovm_do_on
// This macro is used by virtual sequences to execute driver sequences
//-----------------------------------------------------------------------------

`define ovm_do_on(OVM_SEQUENCE_ITEM, SEQUENCER_REF) \
  begin \
  `ovm_create_on(OVM_SEQUENCE_ITEM, SEQUENCER_REF) \
  start_item(OVM_SEQUENCE_ITEM); \
  assert(OVM_SEQUENCE_ITEM.randomize()) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM); \
  end

`define ovm_do_seq(OVM_SEQ, SEQR_CONS_IF) \
  begin \
  `ovm_do_on(OVM_SEQ, SEQR_CONS_IF.consumer_seqr) \
  end

`define ovm_do_on_pri(OVM_SEQUENCE_ITEM, SEQUENCER_REF, PRIORITY) \
  begin \
  `ovm_create_on(OVM_SEQUENCE_ITEM, SEQUENCER_REF) \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  assert(OVM_SEQUENCE_ITEM.randomize()) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do action"); \
  end \
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY); \
  end

// Similar to ovm_do with in-line constraints provided as a 2nd argument.
// The user must supply brackets around the constraints.

`define ovm_do_on_with(OVM_SEQUENCE_ITEM, SEQUENCER_REF, CONSTRAINTS) \
  begin \
  `ovm_create_on(OVM_SEQUENCE_ITEM, SEQUENCER_REF) \
  start_item(OVM_SEQUENCE_ITEM);\
  assert(OVM_SEQUENCE_ITEM.randomize() with CONSTRAINTS ) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do_with action"); \
  end\
  finish_item(OVM_SEQUENCE_ITEM);\
  end

`define ovm_do_seq_with(OVM_SEQ, SEQR_CONS_IF, CONSTRAINTS) \
  begin\
  `ovm_do_on_with(OVM_SEQ, SEQR_CONS_IF.consumer_seqr, CONSTRAINTS) \
  end

`define ovm_do_on_pri_with(OVM_SEQUENCE_ITEM, SEQUENCER_REF, PRIORITY, CONSTRAINTS) \
  begin \
  `ovm_create_on(OVM_SEQUENCE_ITEM, SEQUENCER_REF) \
  start_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  assert(OVM_SEQUENCE_ITEM.randomize() with CONSTRAINTS ) else begin \
    ovm_report_warning("RNDFLD", "Randomization failed in ovm_do_with action"); \
  end\
  finish_item(OVM_SEQUENCE_ITEM, PRIORITY);\
  end

