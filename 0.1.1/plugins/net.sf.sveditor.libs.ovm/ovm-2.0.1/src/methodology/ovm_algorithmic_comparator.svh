// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_algorithmic_comparator.svh#6 $
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

// 
// This is the algorithmic comparator class.
//
// It compares two different streams of data of types BEFORE
// and AFTER.
//
// The TRANSFORMER is a functor class which has a single
// method function AFTER transform( input BEFORE b ) -
// typically used to encapsulate an algorithm of some sort.
//
// Matches and mistmatches are reported into terms of AFTER
// transactions
//
// Unlike other comparators, the ovm_algorithmic_comparator can not be
// registered with the ovm_factory because its constructor is
// non-conforming. To register with the factory, a component's
// constructor must declare its first two arguments as:
//
//   function new (string name, ovm_component parent, ...)

class ovm_algorithmic_comparator #( type BEFORE = int ,
                                    type AFTER = int  ,
                                    type TRANSFORMER = int )
  extends ovm_component;

  const static string type_name = "ovm_algorithmic_comparator #(BEFORE,AFTER,TRANSFORMER)";

  typedef ovm_algorithmic_comparator #( BEFORE , 
                                        AFTER , 
                                        TRANSFORMER ) this_type;
  

  // before_export and after_export are the analysis exports
  // for the two streams of data

  ovm_analysis_export #( AFTER ) after_export;
  ovm_analysis_imp #( BEFORE , this_type ) before_export;
 
  local ovm_in_order_class_comparator #( AFTER ) comp;
  local TRANSFORMER m_transformer;
     
  // The constructor takes a handle to an externally
  // constructed transformer, a compulsory name and an
  // optional parent.
  // 
  // The transformer class must have a function called
  // transform of signature after transform( input before b );
  // 
  // We create an instance of the transformer ( rather than
  // making it a genuine policy class with a static
  // transform method ) because we may need to do reset and
  // configuration on the transformer itself.

  function new( TRANSFORMER transformer,
		string name ,
		ovm_component parent );

    super.new( name , parent );
     
    m_transformer = transformer;
    comp = new("comp" , this );
    
    before_export = new("before_analysis_export" , this );
    after_export = new("after_analysis_export" , this );
  endfunction

  virtual function string get_type_name();
    return type_name;
  endfunction

  virtual function void connect();
    after_export.connect( comp.after_export );
  endfunction

  function void write( input BEFORE b );
    comp.before_export.write( m_transformer.transform( b ) );
  endfunction
      
endclass : ovm_algorithmic_comparator
