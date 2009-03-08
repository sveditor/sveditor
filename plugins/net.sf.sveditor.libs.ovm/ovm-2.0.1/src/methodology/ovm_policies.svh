// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_policies.svh#3 $
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

`ifndef OVM_POLICIES_SVH
`define OVM_POLICIES_SVH

// comp, convert and clone policy classes for built in types
// and classes.
// 
// These are for passing in as parameters to standard
// components such as tlm_fifo and in_order_comparator
//

//
// Built in type comparator, converter and clone
//

//----------------------------------------------------------------------
// CLASS ovm_built_in_comp
//----------------------------------------------------------------------
class ovm_built_in_comp #( type T = int );

  static function bit comp( input T a , input T b );
    return a == b;
  endfunction

endclass

//----------------------------------------------------------------------
// CLASS ovm_built_in_converter
//----------------------------------------------------------------------
class ovm_built_in_converter #( type T = int );

  static function string convert2string( input T t );
    string s;
    $sformat( s , "%p" , t );
    return s; 
  endfunction

endclass

//----------------------------------------------------------------------
// class ovm_built_in_clone
//----------------------------------------------------------------------
class ovm_built_in_clone #( type T = int );

  static function T clone( input T from );
    return from;
  endfunction

endclass

//
// Class comparator, converter, clone
//
// Assumes comp, converter and clone functions in all classes
//

//----------------------------------------------------------------------
// CLASS ovm_class_comp
//----------------------------------------------------------------------
class ovm_class_comp #( type T = int );

  static function bit comp( input T a , input T b );
    return a.comp( b );
  endfunction

endclass

//----------------------------------------------------------------------
// CLASS ovm_class_converter
//----------------------------------------------------------------------
class ovm_class_converter #( type T = int );

  static function string convert2string( input T t );
    return t.convert2string();
  endfunction

endclass

//----------------------------------------------------------------------
// CLASS ovm_class_clone
//----------------------------------------------------------------------
class ovm_class_clone #( type T = int );

  static function ovm_object clone( input T from );
    return from.clone();
  endfunction

endclass

`endif // OVM_POLICIES_SVH
