// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_object_globals.svh#7 $
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

`ifndef OVM_OBJECT_GLOBALS_SVH
`define OVM_OBJECT_GLOBALS_SVH

//This bit marks where filtering should occur to remove urm stuff from a
//scope
bit ovm_start_ovm_declarations = 1;

//----------------------------------------------------------------------------
//
// General purpose parameters and typedefs
//
//----------------------------------------------------------------------------
//
//Current problem with large vector inout decls.
parameter OVM_STREAMBITS = 4096; 
typedef logic signed [OVM_STREAMBITS-1:0] ovm_bitstream_t;

//------------------------------------------------------------------------------
//
// Enumerations
//
//------------------------------------------------------------------------------
// Radix definition
parameter OVM_RADIX     = 'hf000000; //4 bits setting the radix

// ovm_radix_enum
// ----------

typedef enum {
   OVM_BIN       = 'h1000000,
   OVM_DEC       = 'h2000000,
   OVM_UNSIGNED  = 'h3000000,
   OVM_OCT       = 'h4000000,
   OVM_HEX       = 'h5000000,
   OVM_STRING    = 'h6000000,
   OVM_TIME      = 'h7000000,
   OVM_ENUM      = 'h8000000,
   OVM_NORADIX   = 0
} ovm_radix_enum;

function string ovm_radix_to_string(ovm_radix_enum radix);
  case(radix)
    OVM_BIN:     return "'b";
    OVM_OCT:     return "'o";
    OVM_DEC:     return "'s";
    OVM_TIME:    return "'u";
    OVM_STRING:  return "'a";
    default: return "'x";
  endcase
endfunction

// ovm_recursion_policy_enum
// ---------------------

typedef enum { 
  OVM_DEFAULT_POLICY = 0, 
  OVM_DEEP           = 'h400, 
  OVM_SHALLOW        = 'h800, 
  OVM_REFERENCE      = 'h1000
 } ovm_recursion_policy_enum;

//------------------------------------------------------------------------------
//
// Parameters
//
//------------------------------------------------------------------------------

parameter OVM_MACRO_NUMFLAGS    = 17;
//A=ABSTRACT Y=PHYSICAL
//F=REFERENCE, S=SHALLOW, D=DEEP
//K=PACK, R=RECORD, P=PRINT, M=COMPARE, C=COPY
//--------------------------- AYFSD K R P M C
parameter OVM_DEFAULT     = 'b000010101010101;
parameter OVM_ALL_ON      = 'b000000101010101;
parameter OVM_FLAGS_ON    = 'b000000101010101;
parameter OVM_FLAGS_OFF   = 0;

//Values are or'ed into a 32 bit value
//and externally
parameter OVM_COPY         = (1<<0);
parameter OVM_NOCOPY       = (1<<1);
parameter OVM_COMPARE      = (1<<2);
parameter OVM_NOCOMPARE    = (1<<3);
parameter OVM_PRINT        = (1<<4);
parameter OVM_NOPRINT      = (1<<5);
parameter OVM_RECORD       = (1<<6);
parameter OVM_NORECORD     = (1<<7);
parameter OVM_PACK         = (1<<8);
parameter OVM_NOPACK       = (1<<9);
//parameter OVM_DEEP         = (1<<10);
//parameter OVM_SHALLOW      = (1<<11);
//parameter OVM_REFERENCE    = (1<<12);
parameter OVM_PHYSICAL     = (1<<13);
parameter OVM_ABSTRACT     = (1<<14);
parameter OVM_READONLY     = (1<<15);
parameter OVM_NODEFPRINT   = (1<<16);

//Extra values that are used for extra methods
parameter OVM_MACRO_EXTRAS  = (1<<OVM_MACRO_NUMFLAGS);
parameter OVM_FLAGS        = OVM_MACRO_EXTRAS+1;
parameter OVM_UNPACK       = OVM_MACRO_EXTRAS+2;
parameter OVM_CHECK_FIELDS = OVM_MACRO_EXTRAS+3;
parameter OVM_END_DATA_EXTRA = OVM_MACRO_EXTRAS+4;


//Get and set methods (in ovm_object). Used by the set/get* functions
//to tell the object what operation to perform on the fields.
parameter OVM_START_FUNCS  = OVM_END_DATA_EXTRA+1;
parameter OVM_SET           = OVM_START_FUNCS+1;
parameter OVM_SETINT        = OVM_SET;
parameter OVM_SETOBJ        = OVM_START_FUNCS+2;
parameter OVM_SETSTR        = OVM_START_FUNCS+3;
parameter OVM_END_FUNCS     = OVM_SETSTR;

//Global string variables
string ovm_aa_string_key;
`endif  //OVM_OBJECT_GLOBALS_SVH
