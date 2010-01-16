// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_pair.svh#5 $
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

`ifndef OVM_PAIR_SVH
`define OVM_PAIR_SVH

//
// paramterized pair classes
//

class ovm_class_pair #( type T1 = int ,
			type T2 = T1 )
  
  extends ovm_transaction;

  typedef ovm_class_pair #( T1 , T2 ) this_type;
  
  const static string type_name = "ovm_class_pair #(T1,T2)";

  T1 first;
  T2 second;

  function new( input T1 f = null , input T2 s = null , string name="");
    super.new(name);
    if( f == null ) begin
      first = new;
    end
    else begin
      first = f;
    end
    if( s == null ) begin
      second = new;
    end
    else begin
      second = s;
    end
  endfunction  
  
  virtual function ovm_object create (string name=""); 
    this_type v;
    v=new(.name(name));
    return v;
  endfunction

  virtual function string get_type_name ();
    return type_name;
  endfunction

  virtual function string convert2string;
    string s;

    $sformat( s , "pair : %s , %s" ,
	      first.convert2string() ,
	      second.convert2string() );
    
    return s;    
  endfunction

  function bit comp( this_type t );
    return t.first.comp( first ) && t.second.comp( second );
  endfunction

  function void copy( input this_type t );
    first.copy( t.first );
    second.copy( t.second );
  endfunction

  virtual function ovm_object clone();
    this_type t;
    t = new;
    t.copy( this );
    return t;
  endfunction
  
endclass

class ovm_built_in_pair #( type T1 = int ,
			   type T2 = T1 )
  
  extends ovm_transaction;

  typedef ovm_built_in_pair #( T1 , T2 ) this_type;
  
  const static string type_name = "ovm_built_in_pair #(T1,T2)";

  T1 first;
  T2 second;
  
  function new(input T1 f, input T2 s, string name="");
    super.new(name);
    first = f;
    second = s;
  endfunction  
  
  virtual function ovm_object create (string name=""); 
    this_type v;
    v=new(first,second,name);
    return v;
  endfunction

  virtual function string get_type_name ();
    return type_name;
  endfunction

  virtual function string convert2string;
    string s;
`ifndef INCA
    $sformat( s , "built-in pair : %p , %p" ,
	      first ,
	      second );
`else
    $sformat( s , "built-in pair : " ,
	      first , " , ",
	      second );
`endif

    return s;
  endfunction

  function bit comp( this_type t );
    return t.first == first && t.second == second;
  endfunction

  function void copy( input this_type t );
    first = t.first;
    second = t.second;
  endfunction
  
  virtual function ovm_object clone();
    this_type t;
    t = new(first,second);
    return t;
  endfunction

endclass

`endif // OVM_PAIR_SVH
