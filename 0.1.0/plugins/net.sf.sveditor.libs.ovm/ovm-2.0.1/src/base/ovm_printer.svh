// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_printer.svh#8 $
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

//------------------------------------------------------------------------------
//
// This file provides the declarations for the following printing classes
//   ovm_printer_knobs       : controls for controlling print output
//   ovm_printer             : default printer object, contains a knob object 
//                              and user print methods and override methods.
//   ovm_table_printer_knobs : knobs specific to table format, derived from
//                             ovm_printer_knobs.
//   ovm_table_printer       : printer for tabular format
//   ovm_tree_printer_knobs  : knobs specific to tree format
//   ovm_tree_printer        : printer for tree format
//   ovm_line_printer        : printer for line format
//
//------------------------------------------------------------------------------
`ifndef OVM_PRINTER_SVH
`define OVM_PRINTER_SVH

// Forward declarations of printer classes
typedef class ovm_printer;
typedef class ovm_tree_printer;
typedef class ovm_table_printer;
typedef class ovm_line_printer;

`include "base/ovm_object.svh"
`include "base/ovm_misc.svh"

parameter OVM_STDOUT = 1;  // Writes to standard out and nc logfile

//------------------------------------------------------------------------------
//
// CLASS: ovm_printer_knobs
//
// Provides standard printer formatting controls.
//------------------------------------------------------------------------------

class ovm_printer_knobs;
  int       column         = 0;      // current column position. This is not a
                                     // user level variable.
  int       max_width      = 999;    // maximum with of a field. Any field that
                                     // requires more characters will be 
                                     // truncated.
  string    truncation     = "+";    // character to indicate a field has been
                                     // truncated.

  bit       header         = 1;      // print the header
  bit       footer         = 1;      // print the footer
  int       global_indent  = 0;      // indentation for any printed line
  bit       full_name      = 1;      // the full name when printing id info
  bit       identifier     = 1;      // print index identifier information
  int       depth          = -1;     // printing depth, -1 is full
  bit       reference      = 1;      // print the reference of an object
  bit       type_name      = 1;      // print object type (for typed objects)
  bit       size           = 1;      // print the size of an object
  ovm_radix_enum default_radix = OVM_HEX;    // for data with no radix set
  int       begin_elements = 5;      // max front indexs of the array to print
                                     // (-1 for no max)
  int       end_elements   = 5;      // max back indexs of the array to print
  bit       show_radix     = 1;      // prepend value with radix
  string    prefix         = "";     // appended to start of each line

  bit       print_fields   = 1;      // Used by the tcl printing

  //where to print
  int       mcd            = OVM_STDOUT; // file descriptor(s) to write to
  bit       sprint         = 0;      // if set, write to string instead of mcd

  //Radix output control
  string    bin_radix      = "'b";
  string    oct_radix      = "'o";
  string    dec_radix      = "'d";
  string    unsigned_radix = "'d";
  string    hex_radix      = "'h";

  extern function string get_radix_str(ovm_radix_enum radix);
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_printer
//
// Provides a generic printer. No formatting is done, the information is 
// just printed in a raw form.
//------------------------------------------------------------------------------

class ovm_printer;
  protected bit m_array_stack[$];
  ovm_scope_stack    m_scope  = new;  //for internal use
  string             m_string = "";   //for internal use

  ovm_printer_knobs  knobs = new;

  // Primary derived class overrides. Use these methods to create a new 
  // printer type. Functions needed for array printing are not protected
  // since array printing must be done in macros.
  extern virtual  function void print_header       ();
  extern virtual  function void print_footer       ();
  extern virtual protected function void print_id           (string      id, 
                                         byte        scope_separator=".");
  extern virtual protected function void print_type_name    (string      name, bit is_object=0);
  extern virtual protected function void print_size         (int         size=-1);
  extern virtual protected function void print_newline      (bit         do_global_indent=1);
  extern virtual protected function void print_value        (ovm_bitstream_t value, 
                                         int         size, 
                                         ovm_radix_enum  radix=OVM_NORADIX);
  extern virtual protected function void print_value_object (ovm_object  value);
  extern virtual protected function void print_value_string (string      value);

  extern virtual  function void print_value_array  (string      value="", 
                                         int         size=0);
  extern virtual  function void print_array_header ( string      name,
                                         int         size,     
                                         string      arraytype="array",
                                         byte        scope_separator=".");
  extern virtual  function void print_array_range  (int         min,      
                                         int         max);
  extern virtual  function void print_array_footer (int         size=0);

  // Utility methods, may be overridden.
  extern virtual protected function void indent             (int         depth, 
                                         string      indent_str="  ");

  // Primary user level functions. These functions are called from 
  // ovm_object::print() methods, or are called directly on any data to
  // get formatted printing.
  extern virtual function void print_field         ( string      name, 
                                         ovm_bitstream_t value, 
                                         int         size, 
                                         ovm_radix_enum  radix=OVM_NORADIX,
                                         byte        scope_separator=".",
                                         string      type_name="");
  extern virtual function void print_object_header ( string      name,
                                         ovm_object  value, 
                                         byte        scope_separator=".");
  extern virtual function void print_object        (string      name,
                                         ovm_object  value, 
                                         byte        scope_separator=".");
  extern virtual function void print_string        (string      name,
                                         string      value, 
                                         byte        scope_separator=".");
  extern virtual function void print_time          ( string      name,
                                         time        value, 
                                         byte        scope_separator=".");
  extern virtual function void print_generic       (string      name, 
                                         string      type_name, 
                                         int         size, 
                                         string      value,
                                         byte        scope_separator=".");

  // Utility methods
  extern  function bit    istop             ();
  extern  function int    index             (string name);
  extern  function string index_string      (int index, 
                                         string      name="");
  extern protected function void   write_stream      (string str);
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_hier_printer_knobs
//
// Knobs for hierarchical printing. These are knobs which are common to any
// hierarchy printing control.
//------------------------------------------------------------------------------
class ovm_hier_printer_knobs extends ovm_printer_knobs;
  // Add an indentation string for indenting hierarchy instead of 
  // printing full names.
  string   indent_str    = "  ";    // string to use for indentation
  bit      show_root      = 0;      // show full name of the very first object

  extern function new(); 
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_table_printer_knobs
//
// Table printing knobs. Specifies the length of the columns.
//------------------------------------------------------------------------------

class ovm_table_printer_knobs extends ovm_hier_printer_knobs;
  int            name_width  = 25;      // characters in the name column
  int            type_width  = 20;      // characters in the type column
  int            size_width  = 5;       // characters in the size column
  int            value_width = 20;      // characters in the value column
endclass

//------------------------------------------------------------------------------
//
// CLASS: ovm_table_printer
//
// Table printer prints output in a tabular format.
//------------------------------------------------------------------------------

class ovm_table_printer extends ovm_printer;
  extern  function new(); 

  // Adds column headers
  extern virtual function void print_header       ();
  extern virtual function void print_footer       ();

  // Puts information in column format
  extern virtual function void print_id           (string      id,
                                        byte        scope_separator=".");
  extern virtual function void print_size         (int         size=-1);
  extern virtual function void print_type_name    (string      name, bit is_object=0);
  extern virtual function void print_value        (ovm_bitstream_t value, 
                                        int         size, 
                                        ovm_radix_enum  radix=OVM_NORADIX);
  extern virtual function void print_value_object (ovm_object  value);
  extern virtual function void print_value_string (string      value);
  extern virtual function void print_value_array  (string      value="", 
                                        int         size=0);

  //override the knobs variable to allow direct access
  ovm_table_printer_knobs knobs = new;
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_tree_printer_knobs
//
// Tree printing knobs. Specifies the hierarchy separator.
//------------------------------------------------------------------------------

class ovm_tree_printer_knobs extends ovm_hier_printer_knobs;
  string            separator     = "{}";    // the separator for composites
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_tree_printer
//
// Tree printer prints output in a tree format.
//------------------------------------------------------------------------------

class ovm_tree_printer extends ovm_printer;
  // Information to print at the opening/closing of a scope
  extern virtual function void print_scope_open   ();
  extern virtual function void print_scope_close  ();

  // Puts information in tree format
  extern virtual function void print_id           (string id,
                                        byte   scope_separator=".");
  extern virtual function void print_type_name    (string name, bit is_object=0);
  extern virtual function void print_object_header(string      name,
                                        ovm_object  value, 
                                        byte        scope_separator=".");
  extern virtual function void print_object       (string      name,
                                        ovm_object  value, 
                                        byte        scope_separator=".");
  extern virtual function void print_string       ( string      name,
                                        string      value, 
                                        byte        scope_separator=".");
  extern virtual function void print_value_object (ovm_object value);
  extern virtual function void print_value_array  (string      value="", 
                                        int         size=0);
  extern virtual function void print_array_footer (int         size=0);

  extern function new(); 

  //override the knobs variable to allow direct access
  ovm_tree_printer_knobs knobs = new;
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_line_printer
//
// Tree printer prints output in a line format.
//------------------------------------------------------------------------------

class ovm_line_printer extends ovm_tree_printer;
  extern virtual function void print_newline      (bit do_global_indent=1);
  extern  function new(); 
endclass


// Package global printer objects
ovm_table_printer ovm_default_table_printer = new();
ovm_tree_printer  ovm_default_tree_printer  = new();
ovm_line_printer  ovm_default_line_printer  = new();

ovm_printer       ovm_default_printer = ovm_default_table_printer;


`endif
