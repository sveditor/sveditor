// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_object.svh#22 $
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


/*******************************************************************************

  FILE        : ovm_object.svh

  The base class for all urm classes. 

  The ovm_void class is added as an empty root class so that users can
  derive from that class and create datastructures which take both
  ovm_object types as well as user defined types.

 *******************************************************************************/

`ifndef OVM_OBJECT_SVH
`define OVM_OBJECT_SVH

`include "base/ovm_misc.svh"
`include "base/ovm_object_globals.svh"

typedef class ovm_copy_map;
typedef class ovm_printer;
typedef class ovm_comparer;
typedef class ovm_packer;
typedef class ovm_recorder;
typedef class ovm_report_object;
typedef class ovm_object_wrapper;

//------------------------------------------------------------------------------
//
// CLASS: ovm_status_container
//
// Class to contain status information for automation methods.
//
//------------------------------------------------------------------------------

typedef class ovm_object;

// This container class needs to be defined ahead of the ovm_object class
// which uses it to work around a but in ius 6.11 regarding class in packages.
// This class is just for internal usage. It is a class instead of a struct
// becauses structs currently cannot hold class object handles.
class ovm_status_container;
  //Since there is a cost to saving the field string, only do so if needed.
  static bit          save_last_field = 0;
  static string       last_field     = "";

  static bit          warning    = 0;
  static bit          status     = 0;
  static ovm_bitstream_t  bitstream  = 0;
  static int          intv       = 0;
  static int          element    = 0;
  static string       stringv    = "";
  static string       scratch1   = "";
  static string       scratch2   = "";
  static string       key        = "";
  static ovm_object   object     = null;
  static bit          array_warning_done = 0;
  static ovm_scope_stack scope       = init_scope();  //For get-set operations

  extern static function string get_full_scope_arg ();
  extern static function ovm_scope_stack init_scope();
endclass

//------------------------------------------------------------------------------
//
// CLASS: ovm_object
//
// Base class for OVM elements.
//
//------------------------------------------------------------------------------

virtual class ovm_object extends ovm_void;
  //Constructor
  extern function new (string name="");

  //Static bits used for controlling global seeding behaviors
  static  bit use_ovm_seeding  = 1;  //use the URM random stability feature

  //Functions which should not be overridden
  extern  function void          print         (ovm_printer printer=null);
  extern  function string        sprint        (ovm_printer printer=null); 
  extern  function void          reseed        ();

  //Virtual method which can be overridden.
  extern virtual function void   do_print      (ovm_printer printer);
  extern virtual function string do_sprint     (ovm_printer printer); 
  extern virtual function void   do_record     (ovm_recorder recorder);
  extern virtual function void   do_copy       (ovm_object  rhs);
  extern virtual function bit    do_compare    (ovm_object  rhs,
                                                ovm_comparer comparer);
  extern virtual function void   do_pack       (ovm_packer   packer);
  extern virtual function void   do_unpack     (ovm_packer   packer);

  extern virtual function void   set_name      (string      name);

  extern virtual function string get_name      ();
  extern virtual function string get_full_name ();

  extern virtual function int    get_inst_id   ();
  extern static  function int    get_inst_count();

  extern static function ovm_object_wrapper get_type ();

  //Required overrides
  virtual function ovm_object  create        (string name=""); return null; endfunction
  virtual function string      get_type_name (); return "<unknown>"; endfunction

  extern virtual function ovm_object  clone   ();

  //Data oriented methods
  extern  function void         copy          (ovm_object       rhs);
  extern  function bit          compare       (ovm_object       rhs,
                                               ovm_comparer     comparer=null);
  extern  function void         record        (ovm_recorder     recorder=null);

  extern  function int          pack          (ref   bit        bitstream[],
                                               input ovm_packer packer=null);
  extern  function int          unpack        (ref   bit        bitstream[],
                                               input ovm_packer packer=null);
  extern  function int          pack_bytes    (ref   byte unsigned bytestream[],
                                               input ovm_packer packer=null);
  extern  function int          unpack_bytes  (ref   byte unsigned bytestream[],
                                               input ovm_packer packer=null);
  extern  function int          pack_ints     (ref   int unsigned intstream[],
                                               input ovm_packer packer=null);
  extern  function int          unpack_ints   (ref   int unsigned intstream[],
                                               input ovm_packer packer=null);

  extern local function void m_pack(inout ovm_packer packer);
  extern local function void m_unpack_pre(inout ovm_packer packer);
  extern local function void m_unpack_post(ovm_packer packer);

  //The print_matches bit causes an informative message to be printed
  //when a field is set using one of the set methods.
  static  bit print_matches = 0;

  extern static  function void  print_field_match 
                                              (string  fnc,
                                               string      match);

  extern virtual function void  set_int_local 
                                              (string      field_name,
                                               ovm_bitstream_t value,
                                               bit         recurse=1);
  extern virtual function void  set_object_local
                                              (string      field_name,
                                               ovm_object  value,
                                               bit         clone=1,
                                               bit         recurse=1);
  extern virtual function void  set_string_local
                                              (string      field_name,
                                               string      value,
                                               bit         recurse=1);


  // internal methods & properties; users must not use directly
  extern virtual function void     m_field_automation
                                         (ovm_object  tmp_data__,  
                                          int         what__, 
                                          string      str__);
  extern protected function int m_do_data
                                         (      string      arg,
                                          inout ovm_bitstream_t lhs,
                                          input ovm_bitstream_t rhs,
                                                int         what,
                                                int         bits,
                                                int         flag);
  extern protected function int m_do_data_object
                                         (      string      arg,
                                          inout ovm_object  lhs,
                                          input ovm_object  rhs,
                                                int         what,
                                                int         flag);
  extern protected function int m_do_data_string
                                         (      string      arg,
                                          inout string      lhs,
                                          input string      rhs,
                                                int         what,
                                                int         flag);
  extern protected function void m_record_field_object 
                                         (string       arg,
                                          ovm_object   value,
                                          ovm_recorder recorder=null,
                                          int          flag=OVM_DEFAULT);
  extern protected function int m_do_set        
                                         (string       match,
                                          string       arg,
                                          inout ovm_bitstream_t  lhs, 
                                          input int          what,
                                                int          flag);
  extern protected function int m_do_set_string 
                                         (string       match,
                                          string       arg,
                                          inout  string       lhs, 
                                          input  int          what,
                                                 int          flag);
  extern protected function int m_do_set_object 
                                         (string       match,
                                          string       arg,
                                          inout  ovm_object   lhsobj, 
                                          input  int          what,
                                                 int          flag);
  extern protected function string   m_get_function_type  (int what);
  static protected int     m_inst_count = 0;
  local            int     m_inst_id;

  extern protected virtual function ovm_report_object m_get_report_object();

  // internal properties (user should not access directly)
  // needs to be protected since set_name()/get_name() are virtual
  local string m_leaf_name;

  extern static function ovm_status_container init_status();

  // Some urm class need access to this container, so provide a
  // backdoor access.
  static protected ovm_status_container m_sc = init_status();
  static function ovm_status_container m_get_status(); return m_sc; endfunction

  // The following members are used for verifying the integrity of the 
  // ovm_field macros.
  static protected int m_field_array[string];
  extern protected function void m_do_field_check(string field);
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_copy_map
//
//------------------------------------------------------------------------------

// Used to map rhs to lhs so when a cycle is found in the rhs, the correct
// lhs object can be bound to it.
class ovm_copy_map;
  local ovm_object m_map[ovm_object];
  function void set(ovm_object key, ovm_object obj);
    m_map[key] = obj;
  endfunction
  function ovm_object get(ovm_object key);
    if (m_map.exists(key))
       return m_map[key];
    return null;
  endfunction
  function void clear();
    m_map.delete();
  endfunction 
  function void delete(ovm_object v);
    m_map.delete(v);
  endfunction 
endclass

//------------------------------------------------------------------------------
//
// CLASSES: Policy classes
//
// Policy classes for ovm_object basic functions: copy, compare,
// pack/unpack, and record.
//
//------------------------------------------------------------------------------


// ovm_comparer
// ---------------

class ovm_comparer;

  //Comparison message settings
  int unsigned   show_max      = 1;    // Maximum miscompares to print
  int unsigned   verbosity     = OVM_LOW;  // Verbosity setting for miscompare
  ovm_severity   sev           = OVM_INFO; // Severity setting for miscompare
  string         miscompares   = "";   // Last set of miscompares

  //Comparison settings
  bit physical     = 1; // compare physical fields 
  bit abstract     = 1; // compare abstract fields
  bit check_type   = 1; // verify that object types match

  ovm_recursion_policy_enum policy = OVM_DEFAULT_POLICY;

  //Result of comparison
  int unsigned result          = 0; // Count of miscompares, will be <= show_max

  //Methods used checking for printing information
  extern virtual function bit  compare_field  (string      name, 
                                               ovm_bitstream_t lhs, 
                                               ovm_bitstream_t rhs, 
                                               int         size,
                                               ovm_radix_enum  radix=OVM_NORADIX); 
  //For efficency, have a version for smaller fields. Automatically called
  //by compare_field if size is <= 64.
  extern virtual function bit  compare_field_int  (string      name, 
                                               logic[63:0] lhs, 
                                               logic[63:0] rhs, 
                                               int         size,
                                               ovm_radix_enum  radix=OVM_NORADIX); 
  extern virtual function bit  compare_object (string      name,
                                               ovm_object    lhs,
                                               ovm_object    rhs);
  extern virtual function bit  compare_string (string      name,
                                               string      lhs,
                                               string      rhs);

  extern  function void print_rollup    (ovm_object rhs, ovm_object lhs);

  extern  function void print_msg       (string     msg);
  extern  function void print_msg_object(ovm_object   lhs, ovm_object   rhs);

  extern static function ovm_comparer init();

  //Internally used properties
  int depth                    = 0;   //current depth of objects, internal use 
  ovm_copy_map compare_map     = new; //mapping of rhs to lhs objects
  ovm_scope_stack scope        = new;
endclass


// ovm_recorder
// --------------

class ovm_recorder;
  int        recording_depth = 0; 
  integer    tr_handle     = 0;   //transaction handle to record to
  ovm_radix_enum default_radix = OVM_HEX; //radix to use if no radix is set
  bit        physical      = 1;   //record physical fields
  bit        abstract      = 1;   //record abstract fields

  bit        identifier    = 1;   //record object identifiers
  ovm_recursion_policy_enum policy = OVM_DEFAULT_POLICY;
  ovm_scope_stack scope   = new;

  extern virtual function void record_field   (string      name, 
                                               ovm_bitstream_t value, 
                                               int         size, 
                                               ovm_radix_enum  radix=OVM_NORADIX);
  extern virtual function void record_object  (string      name,
                                               ovm_object    value);
  extern virtual function void record_string  (string      name,
                                               string      value);
  extern virtual function void record_time    (string      name,
                                               time        value); 
  extern virtual function void record_generic (string      name, 
                                               string      value);
endclass

// defaults
// --------

ovm_packer       ovm_default_packer     = new();
ovm_comparer     ovm_default_comparer   = ovm_comparer::init();
ovm_recorder     ovm_default_recorder   = new();

// ovm options 
// -----------

class ovm_options_container;
  ovm_comparer    comparer;
  ovm_packer      packer;
  ovm_recorder    recorder;
  ovm_printer     printer;
  bit             clone = 1;
  extern function new();
  extern static function ovm_options_container init();
endclass

`endif //OVM_OBJECT_SVH

