// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_misc.svh#17 $
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

`ifndef OVM_MISC_SVH
`define OVM_MISC_SVH

// Used to indicate "no valid default value" in a parameter
virtual class avm_virtual_class; endclass

//------------------------------------------------------------------------------
//
// CLASS: ovm_void
//
// Empty root class. Acts as a void pointer.
//
//------------------------------------------------------------------------------

virtual class ovm_void;
endclass

// Forward declaration since scope stack uses ovm_objects now
typedef class ovm_object;

//----------------------------------------------------------------------------
//
// CLASS: ovm_scope_stack
//
//----------------------------------------------------------------------------

class ovm_scope_stack;
  local string   m_scope="";
  local string   m_scope_arg="";
  local int      m_depth=0;
  local bit      m_object_map[ovm_void];
  local ovm_void m_stack[$];

  extern function void   set          (string s, ovm_object obj);
  extern function void   down         (string s, ovm_object obj);
  extern function void   down_element (int element, ovm_object obj);
  extern function void   up           (ovm_object obj, byte separator=".");
  extern function void   up_element   (ovm_object obj);
  extern function void   set_arg      (string arg);
  extern function void   unset_arg    (string arg);
  extern function void   set_arg_element  (string arg, int ele);
  extern function int    depth        ();
  extern function string get          ();
  extern function string get_arg      ();
  extern function ovm_object current    ();

  extern function bit    in_hierarchy  (ovm_object obj);
endclass


//----------------------------------------------------------------------------
//
// FUNCTION: ovm_is_match
//
//----------------------------------------------------------------------------
//
// Purpose:
//
//   Match an string, str, with glob string, expr. 
//
// Precondition:
//
//  expr is a string which may contain '*' and '?' characters. A '*'
//  indicates matching zero or more characters (using a greedy compare),
//  '?' indicates matching any single character.
//
// Postcondition:
//
//  Returns a 1 if str matches the expression string and returns
//  0 if it does not match.
//
//----------------------------------------------------------------------------
`ifdef OVM_DPI
import "DPI" function bit ovm_is_match (string expr, string str);
`else
function bit ovm_is_match (string expr, string str);

  int e, es, s, ss;
  string tmp;
  e  = 0; s  = 0;
  es = 0; ss = 0;

  // The ^ used to be used to remove the implicit wildcard, but now we don't
  // use implicit wildcard so this character is just stripped.
  if(expr[0] == "^")
    expr = expr.substr(1, expr.len()-1);

  //This loop is only needed when the first character of the expr may not
  //be a *. 
  while (s != str.len() && expr.getc(e) != "*") begin
    if ((expr.getc(e) != str.getc(s)) && (expr.getc(e) != "?"))
      return 0;
    e++; s++;
  end

  while (s != str.len()) begin
    if (expr.getc(e) == "*") begin
      e++;
      if (e == expr.len()) begin
        return 1;
      end
      es = e;
      ss = s+1;
    end
    else if (expr.getc(e) == str.getc(s) || expr.getc(e) == "?") begin
      e++;
      s++;
    end
    else begin
      e = es;
      s = ss++;
    end
  end
  while (expr.getc(e) == "*")
    e++;
  if(e == expr.len()) begin
    return 1;
  end
  else begin
    return 0;
  end
endfunction
`endif


//----------------------------------------------------------------------------
//
// FUNCTION: ovm_string_to_bits
//
//----------------------------------------------------------------------------

`ifndef OVM_LINE_WIDTH
  `define OVM_LINE_WIDTH 120
`endif 
parameter OVM_LINE_WIDTH = `OVM_LINE_WIDTH;

`ifndef OVM_NUM_LINES
  `define OVM_NUM_LINES 120
`endif
parameter OVM_NUM_LINES = `OVM_NUM_LINES;

parameter OVM_SMALL_STRING = OVM_LINE_WIDTH*8-1;
parameter OVM_LARGE_STRING = OVM_LINE_WIDTH*OVM_NUM_LINES*8-1;

function logic[OVM_LARGE_STRING:0] ovm_string_to_bits(string str);
  $swrite(ovm_string_to_bits, "%0s", str);
endfunction

//----------------------------------------------------------------------------
//
// FUNCTION: ovm_bits_to_string
//
//----------------------------------------------------------------------------

function string ovm_bits_to_string(logic [OVM_LARGE_STRING:0] str);
  $swrite(ovm_bits_to_string, "%0s", str);
endfunction


//----------------------------------------------------------------------------
//
// TASK: ovm_wait_for_nba_region
//
// Call this task to wait for a delta cycle. Program blocks don't have an nba
// so just delay for a #0 in a program block.
//----------------------------------------------------------------------------

task ovm_wait_for_nba_region;

  string s;

  bit nba;
  bit nba_scheduled;

  //If `included directly in a program block, can't use a non-blocking assign,
  //but it isn't needed since program blocks are in a seperate region.
`ifndef OVM_PROGRAM_BLOCK
  if (nba_scheduled == 0) begin
    nba_scheduled = 1;
    nba = 0;
    nba <= 1;
    @(posedge nba) nba_scheduled = 0;
  end
  else begin
    @(posedge nba);
  end
`else
  #0;
`endif

endtask


`endif // OVM_MISC_SVH
