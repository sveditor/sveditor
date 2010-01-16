// $Id: //dvt/vtech/dev/main/ovm/src/tlm/tlm_fifos.svh#21 $
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

typedef class tlm_event;

//----------------------------------------------------------------------
// CLASS tlm_fifo
//----------------------------------------------------------------------
class tlm_fifo #(type T = int) extends tlm_fifo_base #(T);

  const static string type_name = "tlm_fifo #(T)";

  //--------------------------------------------------------------------
  // local data
  //--------------------------------------------------------------------
  local mailbox #( T ) m;
  local int m_size;
  protected int m_pending_blocked_gets;

  //--------------------------------------------------------------------
  // constructor (new)
  //--------------------------------------------------------------------
  function new(string name, ovm_component parent = null, int size = 1);
    super.new(name, parent);

    m = new( size );
    m_size = size;
  endfunction

  virtual function string get_type_name();
    return type_name;
  endfunction

  function int size();
    return m_size;
  endfunction
 
  virtual function int used();
    return m.num();
  endfunction

  function bit is_empty();
    return (m.num() == 0);
  endfunction
 
  function bit is_full();
    return (m.num() == m_size);
  endfunction
 
  task put( input T t );
    m.put( t );
    put_ap.write( t );
  endtask

  task get( output T t );
    m_pending_blocked_gets++;
    m.get( t );
    m_pending_blocked_gets--;
    get_ap.write( t );
  endtask
  
  task peek( output T t );
    m.peek( t );

    get_ap.write( t );
  endtask
   
  function bit try_get( output T t );
    if( !m.try_get( t ) ) begin
      return 0;
    end

    get_ap.write( t );
    return 1;
  endfunction 
  
  function bit try_peek( output T t );
    if( !m.try_peek( t ) ) begin
      return 0;
    end
  
    get_ap.write( t );
    return 1;
  endfunction

  function bit try_put( input T t );
    if( !m.try_put( t ) ) begin
      return 0;
    end
  
    put_ap.write( t );
    return 1;
  endfunction  

  function bit can_put();
    return m_size == 0 || m.num() < m_size;
  endfunction  

  function bit can_get();
    return m.num() > 0 && m_pending_blocked_gets == 0;
  endfunction
  
  function bit can_peek();
    return m.num() > 0;
  endfunction

  function void flush();
    T t;
    bit r;

    r = 1; 
    while( r ) r = try_get( t ) ;
    
    if( m.num() > 0 && m_pending_blocked_gets != 0 ) begin
      ovm_report_error("flush failed" ,
		       "there are blocked gets preventing the flush");
    end
  
  endfunction
 
endclass 

//----------------------------------------------------------------------
// CLASS tlm_analysis_fifo
//----------------------------------------------------------------------

// An tlm_analysis_fifo is an unbounded tlm_fifo that also implements and 
// exports the write interfaces.
//
// It is very useful in objects such as scoreboards which need to be
// connected to monitors.

class tlm_analysis_fifo #(type T = int) extends tlm_fifo #(T);

  ovm_analysis_imp #(T, tlm_analysis_fifo #(T)) analysis_export;

  function new(string name ,  ovm_component parent = null);
    super.new(name, parent, 0); // analysis fifo must be unbounded

    analysis_export = new("analysis_export", this);

  endfunction

  const static string type_name = "tlm_analysis_fifo #(T)";

  virtual function string get_type_name();
    return type_name;
  endfunction

  function void write(input T t);
    void'(this.try_put(t)); // unbounded => must succeed
  endfunction

endclass
