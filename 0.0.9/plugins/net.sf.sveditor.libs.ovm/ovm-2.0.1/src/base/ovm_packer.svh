// $Id: ovm_packer.svh,v 1.9 2008/10/09 15:17:56 jlrose Exp $
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

  FILE        : ovm_packer.svh

  This class provides the packing/unpacking policy for data objects.

 *******************************************************************************/

`ifndef OVM_PACKER_SVH
`define OVM_PACKER_SVH


// ovm_packer
// ------------

class ovm_packer;
  static bit bitstream[];        //local bits for (un)pack_bytes
  static bit fabitstream[];      //field automation bits for (un)pack_bytes
  int count               = 0;   //used to count the number of packed bits
  ovm_scope_stack scope   = new;

  bit   use_metadata  = 0;  //insert metadata for dynamic fields
  bit   physical      = 1;  //pack/unpack physical fields by default
  bit   abstract      = 0;  //don't pack abstract fields by default
  bit   big_endian    = 1;  //load pack array from left to right
  bit   reverse_order = 0;  //flip the bit order around
  byte  byte_size     = 8;  //set up bytesize for endianess
  int   word_size     = 16; //set up worksize for endianess
  bit   nopack        = 0;  //only count packable bits

  ovm_recursion_policy_enum policy = OVM_DEFAULT_POLICY;

  bit [OVM_STREAMBITS*8-1:0] m_bits = 0;
  int m_packed_size  = 0;

  // User interface for packing data into a bitstream
  extern virtual function void pack_field_int (logic[63:0] value, int size);
  extern virtual function void pack_field     (ovm_bitstream_t value, int size);
  extern virtual function void pack_string    (string value);
  extern virtual function void pack_time      (time value); 
  extern virtual function void pack_real      (real value);
  extern virtual function void pack_object    (ovm_object value);

  // User interface for unpacking data from a bitstream
  extern virtual function bit         is_null          ();
  extern virtual function logic[63:0] unpack_field_int (int size);
  extern virtual function ovm_bitstream_t unpack_field     (int size);
  extern virtual function string      unpack_string    (int num_chars=-1);
  extern virtual function time        unpack_time      (); 
  extern virtual function real        unpack_real      ();
  extern virtual function void unpack_object_ext  (inout ovm_object value);
  extern virtual function void        unpack_object    (ovm_object value);

  extern virtual function int get_packed_size(); 

  // methods primarily for internal use

  extern virtual function ovm_bitstream_t get_packed_bits ();

  extern virtual function bit  unsigned get_bit  (int unsigned index);
  extern virtual function byte unsigned get_byte (int unsigned index);
  extern virtual function int  unsigned get_int  (int unsigned index);

  extern virtual function void get_bits (ref bit unsigned bits[]);
  extern virtual function void get_bytes(ref byte unsigned bytes[]);
  extern virtual function void get_ints (ref int unsigned ints[]);

  extern virtual function void put_bits (ref bit unsigned bitstream[]);
  extern virtual function void put_bytes(ref byte unsigned bytestream[]);
  extern virtual function void put_ints (ref int unsigned intstream[]);

  extern virtual function void set_packed_size(); 
  extern function void index_error(int index, string id, int sz);
  extern function bit enough_bits(int needed, string id);

  extern function void reset();

endclass

`endif //OVM_OBJECT_SVH

