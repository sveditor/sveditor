// $Id: //dvt/vtech/dev/main/ovm/src/methodology/ovm_in_order_comparator.svh#9 $
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

//----------------------------------------------------------------------
// CLASS in_order_comparator
//
// in_order_comparator : compares two streams of data
//
// makes no assumptions about the relative ordering of the two streams
//
// T is the type of the two streams of data.
//
// comp and convert are functors which describe how to do
// comparison and printing for T.
//
// These parameters can be changed for different T's :
// however, we expect that the two pairs of classes above
// will be OK for most cases. Built in types ( such as ints,
// bits, logic, and structs ) are dealt with by using the
// default functors built_in_comp and built_in_converter, while
// classes should be dealt with by class_comp and
// class_converter, which in turn assume the existence of comp
// and convert2string functions in the class itself.
//----------------------------------------------------------------------

class ovm_in_order_comparator 
  #( type T = int ,
     type comp_type = ovm_built_in_comp #( T ) ,
     type convert = ovm_built_in_converter #( T ) , 
     type pair_type = ovm_built_in_pair #( T ) )
    extends ovm_component;

  typedef ovm_in_order_comparator #(T,comp_type,convert,pair_type) this_type;
  `ovm_component_param_utils(this_type)

  const static string type_name = 
    "ovm_in_order_comparator #(T,comp_type,convert,pair_type)";

  //  The two exports. Actually, there are no assumptions made about
  // ordering, so it doesn't matter which way around you make the 
  // connections

  ovm_analysis_export #( T ) before_export , after_export;
  ovm_analysis_port #( pair_type ) pair_ap;
  
  local tlm_analysis_fifo #( T ) before_fifo , after_fifo;
  int m_matches , m_mismatches;


  function new( string name ,
		ovm_component parent ) ;

    super.new( name, parent );

    before_export = new("before_export" , this );
    after_export = new("after_export" , this );

    pair_ap = new("pair_ap" , this );
    
    before_fifo = new("before" , this );
    after_fifo = new("after" , this );
    
    m_matches = 0;
    m_mismatches = 0;
  endfunction
  
  virtual function string get_type_name();
    return type_name;
  endfunction

  virtual function void connect();
    before_export.connect( before_fifo.analysis_export );
    after_export.connect( after_fifo.analysis_export );
  endfunction


  // run is not a user visible task. It gets pairs of befores and
  // afters, and compares them. Status info is updated according to the
  // results of this comparison.

  virtual task run();
 
    pair_type pair;
    T b;
    T a;
  
    string s;
   
    forever begin
      
      before_fifo.get( b );
      after_fifo.get( a );
      
      if( !comp_type::comp( b , a ) ) begin

      $sformat( s , "%s differs from %s" ,
          convert::convert2string( a ) ,
          convert::convert2string( b ) );
    
        ovm_report_warning("Comparator Mismatch" , s );
        m_mismatches++;
      end
      else begin
        s = convert::convert2string( b );
        ovm_report_info("Comparator Match" , s );
        m_matches++;
      end

      //
      // we make the assumption here that a transaction "sent for
      // analysis" is safe from being edited by another process
      //
      // hence, it is safe not to clone a and b.
      
      pair = new( a , b );
      pair_ap.write( pair );
    end
  
  endtask

  virtual function void flush();
    m_matches = 0;
    m_mismatches = 0;
  endfunction
  
endclass : ovm_in_order_comparator

//----------------------------------------------------------------------
// CLASS in_order_built_in_comparator
//----------------------------------------------------------------------

// in_order_built_in_comparator uses the default ( ie,
// built_in ) comparison and printing policy classes.

class ovm_in_order_built_in_comparator #( type T = int )
  extends ovm_in_order_comparator #( T );

  typedef ovm_in_order_built_in_comparator #(T) this_type;
  `ovm_component_param_utils(this_type)

  const static string type_name = "ovm_in_order_built_in_comparator #(T)";

  function new( string name , ovm_component parent );
    super.new( name, parent );
  endfunction
  
  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass : ovm_in_order_built_in_comparator 

//----------------------------------------------------------------------
// CLASS in_order_class_comparator
//----------------------------------------------------------------------

// in_order_class_comparator uses the class comparison and
// printing policy classes. This ultimately relies on the
// existence of comp and convert2string methods in the
// transaction type T

class ovm_in_order_class_comparator #( type T = int )
  extends ovm_in_order_comparator #( T , 
                                     ovm_class_comp #( T ) , 
                                     ovm_class_converter #( T ) , 
                                     ovm_class_pair #( T, T ) );

  typedef ovm_in_order_class_comparator #(T) this_type;
  `ovm_component_param_utils(this_type)

  const static string type_name = "ovm_in_order_class_comparator #(T)";

  function new( string name  , ovm_component parent);
    super.new( name, parent );
  endfunction
  
  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass : ovm_in_order_class_comparator
