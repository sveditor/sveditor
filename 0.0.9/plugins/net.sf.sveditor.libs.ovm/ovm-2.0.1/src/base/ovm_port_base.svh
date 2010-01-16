//------------------------------------------------------------------------------
//   Copyright 2007-2008 Mentor Graphics Corporation
//   Copyright 2007-2008 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the "License"); you may not
//   use this file except in compliance with the License.  You may obtain a copy
//   of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
//   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
//   License for the specific language governing permissions and limitations
//   under the License.
//------------------------------------------------------------------------------

typedef enum {
  OVM_PORT ,
  OVM_EXPORT ,
  OVM_IMPLEMENTATION
} ovm_port_type_e;

`const int OVM_UNBOUNDED_CONNECTIONS = -1;
`const string s_connection_error_id = "Connection Error";
`const string s_connection_warning_id = "Connection Warning";
`const string s_spaces = "                       ";

typedef class ovm_port_component_base;
typedef ovm_port_component_base ovm_port_list[string];

//------------------------------------------------------------------------------
//
// CLASS: ovm_port_component_base
//
//------------------------------------------------------------------------------
// This class defines an interface for obtaining a port's connectivity lists
// after or during the end_of_elaboration phase.  The sub-class,
// ovm_port_component #(PORT), implements this interface.
//
// The connectivity lists are returned in the form of handles to objects of this
// type. This allowing traversal of any port's fan-out and fan-in network
// through recursive calls to get_connected_to and get_provided_to. Each port's
// full name and type name can be retrieved using get_full_name and
// get_type_name methods inherited from ovm_component.
//------------------------------------------------------------------------------

virtual class ovm_port_component_base extends ovm_component;
   
  function new (string name, ovm_component parent);
    super.new(name,parent);
  endfunction

  pure virtual function void get_connected_to(ref ovm_port_list list);
  pure virtual function void get_provided_to(ref ovm_port_list list);

  pure virtual function bit is_port();
  pure virtual function bit is_export();
  pure virtual function bit is_imp();

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_port_component #(PORT)
//
//------------------------------------------------------------------------------
// See description of ovm_port_base for information about this class
//------------------------------------------------------------------------------


class ovm_port_component #(type PORT=ovm_void) extends ovm_port_component_base;
   
  PORT m_port;

  function new (string name, ovm_component parent, PORT port);
    super.new(name,parent);
    if (port == null)
      ovm_report_fatal("Bad usage", "Null handle to port");
    m_port = port;
  endfunction

  virtual function string get_type_name();
    if(m_port == null) return "ovm_port_component";
    return m_port.get_type_name();
  endfunction
    
  virtual function void resolve_bindings();
    m_port.resolve_bindings();
  endfunction
    
  function PORT get_port();
    return m_port;
  endfunction

  function void do_display (int max_level=-1, int level=0,
                            bit display_connectors=0);
    m_port.do_display(max_level,level,display_connectors);
  endfunction

  virtual function void get_connected_to(ref ovm_port_list list);
    m_port.get_connected_to(list);
  endfunction

  virtual function void get_provided_to(ref ovm_port_list list);
    m_port.get_provided_to(list);
  endfunction

  function bit is_port ();
    return m_port.is_port();
  endfunction

  function bit is_export ();
    return m_port.is_export();
  endfunction

  function bit is_imp ();
    return m_port.is_imp();
  endfunction

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_port_base #(IF)
//
//------------------------------------------------------------------------------
//
// The base class for ports, exports, and implementations (imps). The template
// parameter, IF, specifies the base interface class for the port.  Derivations
// of this class must then implement that interface.
//
// The ovm_port_base class provides the means to connect the ports together.
// Later, after a process called "binding resolution," each port and export holds
// a list of all imps that connect to it, directly or indirectly via other ports
// and exports. In effect, we are collapsing the port's fanout, which can span
// several levels of hierarchy up and down, into a single array held local to the
// port. When accessing the interface via the port at run-time, the port merely
// looks up the indexed interface in this list and calls the appropriate
// interface method. 
//
// SV does not support multiple inheritance. Thus, two classes are used
// to define a single, logical port: ovm_port_base, which inherits from the
// user's interface class, and ovm_port_component, which inherits from
// ovm_component.  The ovm_port_base class constructor creates an instance of
// the ovm_port_component and passes a handle to itself to its constructor,
// effectively linking the two.
// 
// The OVM provides a complete set of ports, exports, and imps for the OSCI-
// standard TLM interfaces. These can be found in the .../src/tlm/ directory.
//
// get_name
// get_full_name
// get_parent
//   These methods provide the leaf name, the full name, and the handle to the
//   parent component, respectively. The implementations of these methods 
//   delegate to the port's component proxy. 
//
// min_size
// max_size
//   Returns the lower and upper bound on the required number of imp
//   connections.
//
// is_unbounded
//   Returns 1 if the max_size is set to OVM_UNBOUNDED_CONNECTIONS.
//
// is_port
// is_export
// is_imp
//   Returns 1 if true, 0 if false. The port type is a constructor argument.
//
// size
//   Returns the total number of imps connected to this port. The number is
//   only valid at and after the end_of_elaboration phase. It is 0 before then.
//
// set_if
//   Sets the default imp to use when calling an interface method. The default
//   is 0.  Use this to access a specific imp when size() > 0.
//
// connect
//   Binds this port to another port given as an argument after validating the
//   legality of the connection. See the connect and m_check_relationship
//   method implementations for more information.
//
// resolve_bindings
//   This callback is called just before entering the end_of_elaboration phase.
//   It recurses through this port's fanout to determine all the imp destina-
//   tions. It then checks against the required min and max connections.
//   After resolution, size() returns a valid value and set_if() can be used
//   to access a particular imp.
//   
//------------------------------------------------------------------------------

virtual class ovm_port_base #(type IF=ovm_void) extends IF;
   

  typedef ovm_port_base #(IF) this_type;
  
  // local, protected, and non-user properties
  protected int unsigned  m_if_mask;
  protected this_type     m_if;    // REMOVE
  protected int unsigned  m_def_index;
  ovm_port_component #(this_type) m_comp;
  local this_type m_provided_by[string];
  local this_type m_provided_to[string];
  local ovm_port_type_e   m_port_type;
  local int               m_min_size;
  local int               m_max_size;
  local bit               m_resolved;
  local this_type         m_imp_list[string];

  function new (string name,
                ovm_component parent,
                ovm_port_type_e port_type,
                int min_size=0,
                int max_size=1);
    ovm_component comp;
    int tmp;
    m_port_type = port_type;
    m_min_size  = min_size;
    m_max_size  = max_size;
    m_comp = new(name, parent, this);

    if (!m_comp.get_config_int("check_connection_relationships",tmp))
      m_comp.set_report_id_action(s_connection_warning_id, OVM_NO_ACTION);

  endfunction

  function string get_name();
    return m_comp.get_name();
  endfunction

  virtual function string get_full_name();
    return m_comp.get_full_name();
  endfunction

  virtual function ovm_component get_parent();
    return m_comp.get_parent();
  endfunction

  virtual function ovm_port_component_base get_comp();
    return m_comp;
  endfunction

  virtual function string get_type_name();
    case( m_port_type )
      OVM_PORT : return "port";
      OVM_EXPORT : return "export";
      OVM_IMPLEMENTATION : return "implementation";
    endcase
  endfunction

  function int max_size ();
    return m_max_size;
  endfunction

  function int min_size ();
    return m_min_size;
  endfunction

  function bit is_unbounded ();
    return (m_max_size ==  OVM_UNBOUNDED_CONNECTIONS);
  endfunction

  function bit is_port ();
    return m_port_type == OVM_PORT;
  endfunction

  function bit is_export ();
    return m_port_type == OVM_EXPORT;
  endfunction

  function bit is_imp ();
    return m_port_type == OVM_IMPLEMENTATION;
  endfunction

  function int size ();
    return m_imp_list.num();
  endfunction

  function void set_if (int index=0);
    m_if = get_if(index);
    if (m_if != null)
      m_def_index = index;
  endfunction

  function void set_default_index (int index);
    m_def_index = index;
  endfunction


  // connect
  // -------

  function void connect (this_type provider);

    // Check that the provider port meets the interface requirements of this
    // port. Each port has an interface mask that encodes the interface(s) it
    // supports. If the bitwise AND of these masks is equal to the this
    // port's mask, the requirement is met.
  
    if (provider == null) begin
      m_comp.ovm_report_error(s_connection_error_id,
                       "Cannot connect to null port handle");
      return;
    end

    if ((provider.m_if_mask & m_if_mask) != m_if_mask) begin
      m_comp.ovm_report_error(s_connection_error_id, 
          {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") does not provide the complete interface required of this port (type ",
           get_type_name(),")"});
      return;
    end

    // IMP.connect(anything) is illegal
    if (is_imp()) begin
      m_comp.ovm_report_error(s_connection_error_id,
        $psprintf(
"Cannot call an imp port's connect method. An imp is connected only to the component passed in its constructor. (You attempted to bind this imp to %s)", provider.get_full_name()));
      return;
    end
  
    // EXPORT.connect(PORT) are illegal
    if (is_export() && provider.is_port()) begin
      m_comp.ovm_report_error(s_connection_error_id,
        $psprintf(
"Cannot connect exports to ports Try calling port.connect(export) instead. (You attempted to bind this export to %s).", provider.get_full_name()));
      return;
    end
  
    void'(m_check_relationship(provider));
  
    m_provided_by[provider.get_full_name()] = provider;
    provider.m_provided_to[get_full_name()] = this;
    
  endfunction


  // debug_connected_to
  // ------------------

  function void debug_connected_to (int level=0, int max_level=-1);
    int sz, num, curr_num;
    string s_sz;
    static string indent, save;
    this_type port;
  
    if (level <  0) level = 0;
    if (level == 0) begin save = ""; indent="  "; end
  
    if (max_level != -1 && level >= max_level)
      return;
  
    num = m_provided_by.num();
  
    if (m_provided_by.num() != 0) begin
      foreach (m_provided_by[nm]) begin
        curr_num++;
        port = m_provided_by[nm];
        save = {save, indent, "  | \n"};
        save = {save, indent, "  |_",nm," (",port.get_type_name(),")\n"};
        indent = (num > 1 && curr_num != num) ?  {indent, "  | "} : {indent, "    "};
        port.debug_connected_to(level+1, max_level);
        indent = indent.substr(0,indent.len()-4-1);
      end
    end
  
    if (level == 0) begin
      if (save != "")
        save = {"This port's fanout network:\n\n  ",
               get_full_name()," (",get_type_name(),")\n",save,"\n"};
      if (m_imp_list.num() == 0) begin
        if (end_of_elaboration_ph.is_done() || end_of_elaboration_ph.is_in_progress())
          save = {save,"  Connected implementations: none\n"};
        else
        save = {save,"  Connected implementations: not resolved until end-of-elab\n"};
      end
      else begin
        save = {save,"  Resolved implementation list:\n"};
        foreach (m_imp_list[nm]) begin
          port = m_imp_list[nm];
          s_sz.itoa(sz);
          save = {save, indent, s_sz, ": ",nm," (",port.get_type_name(),")\n"};
          sz++;
        end
      end
      m_comp.ovm_report_info("debug_connected_to", save);
    end
  endfunction
  

  // debug_provided_to
  // -----------------

  function void debug_provided_to  (int level=0, int max_level=-1);
    string nm;
    int num,curr_num;
    this_type port;
    static string indent, save;
  
    if (level <  0) level = 0; 
    if (level == 0) begin save = ""; indent = "  "; end

    if (max_level != -1 && level > max_level)
      return;
  
    num = m_provided_to.num();
  
    if (num != 0) begin
      foreach (m_provided_to[nm]) begin
        curr_num++;
        port = m_provided_to[nm];
        save = {save, indent, "  | \n"};
        save = {save, indent, "  |_",nm," (",port.get_type_name(),")\n"};
        indent = (num > 1 && curr_num != num) ?  {indent, "  | "} : {indent, "    "};
        port.debug_provided_to(level+1, max_level);
        indent = indent.substr(0,indent.len()-4-1);
      end
    end

    if (level == 0) begin
      if (save != "")
        save = {"This port's fanin network:\n\n  ",
               get_full_name()," (",get_type_name(),")\n",save,"\n"};
      if (m_provided_to.num() == 0)
        save = {save,indent,"This port has not been bound\n"};
      m_comp.ovm_report_info("debug_provided_to", save);
    end
  
  endfunction


  // get_connected_to
  // ----------------

  function void get_connected_to (ref ovm_port_list list);
    this_type port;
    list.delete();
    foreach (m_provided_by[name]) begin
      port = m_provided_by[name];
      list[name] = port.get_comp();
    end
  endfunction


  // get_provided_to
  // ---------------

  function void get_provided_to (ref ovm_port_list list);
    this_type port;
    list.delete();
    foreach (m_provided_to[name]) begin
      port = m_provided_to[name];
      list[name] = port.get_comp();
    end
  endfunction


  // m_check_relationship
  // --------------------

  local function bit  m_check_relationship (this_type provider);  
    string s;
    this_type from;
    ovm_component from_parent;
    ovm_component to_parent;
    ovm_component from_gparent;
    ovm_component to_gparent;
  
    // Checks that the connection is between ports that are hierarchically
    // adjacent (up or down one level max, or are siblings),
    // and check for legal direction, requirer.connect(provider).

    // if we're an analysis port, allow connection to anywhere
    if (get_type_name() == "ovm_analysis_port")
      return 1;
    
    from         = this;
    from_parent  = get_parent();
    to_parent    = provider.get_parent();
  
    // skip check if we have a parentless port
    if (from_parent == null || to_parent == null)
      return 1;
  
    from_gparent = from_parent.get_parent();
    to_gparent   = to_parent.get_parent();
  
    // Connecting port-to-port: CHILD.port.connect(PARENT.port)
    //
    if (from.is_port() && provider.is_port() && from_gparent != to_parent) begin
      s = {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") is not up one level of hierarchy from this port. ",
           "A port-to-port connection takes the form ",
           "child_component.child_port.connect(parent_port)"};
      m_comp.ovm_report_warning(s_connection_warning_id, s);
      return 0;
    end    
      
    // Connecting port-to-export: SIBLING.port.connect(SIBLING.export)
    // Connecting port-to-imp:    SIBLING.port.connect(SIBLING.imp)
    //
    else if (from.is_port() && (provider.is_export() || provider.is_imp()) &&
             from_gparent != to_gparent) begin
        s = {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") is not at the same level of hierarchy as this port. ",
           "A port-to-export connection takes the form ",
           "component1.port.connect(component2.export)"};
      m_comp.ovm_report_warning(s_connection_warning_id, s);
      return 0;
    end
  
    // Connecting export-to-export: PARENT.export.connect(CHILD.export)
    // Connecting export-to-imp:    PARENT.export.connect(CHILD.imp)
    //
    else if (from.is_export() && (provider.is_export() || provider.is_imp()) &&
             from_parent != to_gparent) begin
      s = {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") is not down one level of hierarchy from this export. ",
           "An export-to-export or export-to-imp connection takes the form ",
           "parent_export.connect(child_component.child_export)"};
      m_comp.ovm_report_warning(s_connection_warning_id, s);
      return 0;
    end

    return 1;
  endfunction


  // m_add_list
  // ----------

  local function void m_add_list           (this_type provider);
    string sz;
    this_type imp;

    for (int i = 0; i < provider.size(); i++) begin
      imp = provider.get_if(i);
      if (!m_imp_list.exists(imp.get_full_name()))
        m_imp_list[imp.get_full_name()] = imp;
    end

  endfunction


  // resolve_bindings
  // ----------------

  function void resolve_bindings();
    if (m_resolved) // don't repeat ourselves
     return;

    if (is_imp()) begin
      m_imp_list[get_full_name()] = this;
    end
    else begin
      foreach (m_provided_by[nm]) begin
        this_type port;
        port = m_provided_by[nm];
        port.resolve_bindings();
        m_add_list(port);
      end
    end
  
    m_resolved = 1;
  
    if (size() < min_size() ) begin
      m_comp.ovm_report_error(s_connection_error_id, 
        $psprintf("connection count of %0d does not meet required minimum of %0d",
        size(), min_size()));
    end
  
    if (max_size() != OVM_UNBOUNDED_CONNECTIONS && size() > max_size() ) begin
      m_comp.ovm_report_error(s_connection_error_id, 
        $psprintf("connection count of %0d exceeds maximum of %0d",
        size(), max_size()));
    end

    if (size())
      set_if(0);
  
  endfunction
  

  `include "compatibility/urm_port_compatibility.svh"

  // get_if
  // ------

  function ovm_port_base #(IF) get_if(int index=0);
    string s;
    if (size()==0) begin
      m_comp.ovm_report_warning("get_if",
        "Port size is zero; cannot get interface at any index");
      return null;
    end
    if (index < 0 || index >= size()) begin
      $sformat(s, "Index %0d out of range [0,%0d]", index, size()-1);
      m_comp.ovm_report_warning(s_connection_error_id, s);
      return null;
    end
    foreach (m_imp_list[nm]) begin
      if (index == 0)
        return m_imp_list[nm];
      index--;
    end
  endfunction



  //------------------------------------
  // Deprecated members below this point


  function this_type lookup_indexed_if(int i=0);
    return get_if(i);
  endfunction

  function void do_display (int max_level=-1, int level=0,
                            bit display_connectors=0);
    if (display_connectors)
      m_comp.ovm_report_info("hierarchy debug" , "" , 1000 );
  endfunction

  function void remove();
    return;
  endfunction

  local function bit check_phase (this_type provider);
    return 1;
  endfunction

  local function void check_min_connection_size ();
    return;
  endfunction

endclass

