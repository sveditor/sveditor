// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_factory.svh#14 $
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

`ifndef OVM_FACTORY_SVH
`define OVM_FACTORY_SVH

typedef class ovm_object;
typedef class ovm_component;

//------------------------------------------------------------------------------
//
// CLASS: ovm_object_wrapper (OVM)
//
//------------------------------------------------------------------------------

// To register with a factory, a class must create a wrapper which implements
// either the create_object (for generic data object) or create_component (for
// hierarchical elements).

virtual class ovm_object_wrapper;

  virtual function ovm_object create_object (string name="");
    return null;
  endfunction

  virtual function ovm_component create_component (string name, 
                                                   ovm_component parent); 
    return null;
  endfunction

  // Subtypes must specify the type that it creates
  pure virtual function string get_type_name();

endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_factory_override
//
//------------------------------------------------------------------------------

class ovm_factory_override;
  string full_inst_path;
  string orig_type_name;
  string ovrd_type_name;
  ovm_object_wrapper orig_type;
  ovm_object_wrapper ovrd_type;
  function new (string full_inst_path="",
                string orig_type_name="",
                ovm_object_wrapper orig_type=null,
                ovm_object_wrapper ovrd_type);
    assert (ovrd_type != null);
    this.full_inst_path= full_inst_path;
    this.orig_type_name = orig_type == null ? orig_type_name : orig_type.get_type_name();
    this.orig_type      = orig_type;
    this.ovrd_type_name = ovrd_type.get_type_name();
    this.ovrd_type      = ovrd_type;
  endfunction
endclass


//------------------------------------------------------------------------------
//
// CLASS: ovm_factory
//
//------------------------------------------------------------------------------
//
// Type-based factory configuration (preferred)
//
//
// String-based factory configuration
//
// set_type_override
//
//    Configures the factory to produce an object of type 'override_type_name'
//    when a request is made using 'requested_type_name', which often is the
//    base type but can be any arbitrary string.
//
//      set_type_override("driver", "my_driver")
//
//    This says: "When a request for 'driver' is made, produce and return an
//    object whose type name is 'my_driver'." Overrides are recursive. That is:
//
//      set_type_override("my_driver", "special_driver")
//
//    This says: "When a request for 'driver' or 'my_driver' is made, produce
//    and return an object whose type name is 'special_driver'." 
//
//    This says: "When a request for 'driver' or 'my_driver' is made, produce
//    and return an object whose type name is 'special_driver'." 
//
// set_inst_override
//
//    Configures the factory to produce an object of type 'override_type_name'
//    when a request is made using 'requested_type_name' *and* 
//      {parent_inst_path,".",name}
//    matches the 'inst_path' string. The 'inst_path' string allows overrides
//    to occur on an instance basis. It may contain wildcards so as to apply to
//    more than one context. The 'requested_type_name' is often the base type
//    but can be any arbitrary string.
//
//      set_inst_override("top.a1.master", "some_monitor", "really_special_monitor")
//      set_inst_override("top.*.master",  "some_monitor", "special_monitor")
//      set_type_override("some_monitor",  "basic_monitor")
//
//    This says: "When a request for 'some_monitor' is made, produce 
//    'really_special_monitor' when the context is 'top.a1.master',
//    'special_monitor' when the context is 'top.*.master', and 'basic_monitor'
//    in every other context." Note how the order goes from most specific to
//    most general. That's important. A type override can be expressed as
//    an instance override. The following is equivalent to, although less
//    efficient than, the type override above:
//
//      set_inst_override("*", "some_monitor",  "basic_monitor")
//
//    Because the requested_type_name does not necessarily represent the type
//    name of an actual class, the factory *must* be configured to map it to some
//    concreate type, else a run-time error will occur when a request is made using
//    'some_monitor' as the original_type_name.
//
//
// create_object
// create_component
//    Methods for creating objects
//
// auto_register
//    Method for registering an object creator. This is called automatically
//    by the `ovm_*_utils macros
//
//------------------------------------------------------------------------------

class ovm_factory;

  extern `_protected function new ();

  extern static function ovm_factory get();


  extern function void          set_inst_override_by_type(ovm_object_wrapper original_type,
                                                         ovm_object_wrapper override_type,
                                                         string full_inst_path);

  extern function void          set_type_override_by_type(ovm_object_wrapper original_type,
                                                         ovm_object_wrapper override_type,
                                                         bit replace=1);

  extern function ovm_object    create_object_by_type   (ovm_object_wrapper requested_type,  
                                                         string parent_inst_path="",
                                                         string name=""); 

  extern function ovm_component create_component_by_type(ovm_object_wrapper requested_type,  
                                                         string parent_inst_path="",
                                                         string name, 
                                                         ovm_component parent);
  extern
    function ovm_object_wrapper find_override_by_type   (ovm_object_wrapper requested_type,
                                                         string full_inst_path);

  extern function void          debug_create_by_type    (ovm_object_wrapper requested_type,
                                                         string parent_inst_path="",
                                                         string name="");


  extern function void          set_inst_override_by_name(string original_type_name,
                                                         string override_type_name,
                                                         string full_inst_path);

  extern function void          set_type_override_by_name(string original_type_name,
                                                         string override_type_name,
                                                         bit replace=1);

  extern function ovm_object    create_object_by_name   (string requested_type_name,  
                                                         string parent_inst_path="",
                                                         string name=""); 

  extern function ovm_component create_component_by_name(string requested_type_name,  
                                                         string parent_inst_path="",
                                                         string name, 
                                                         ovm_component parent);
  extern
    function ovm_object_wrapper find_override_by_name   (string requested_type_name,
                                                         string full_inst_path);

  extern
    function ovm_object_wrapper find_by_name            (string type_name);

  extern function void          debug_create_by_name    (string requested_type_name,
                                                         string parent_inst_path="",
                                                         string name="");


  extern function void          print                   (int all_types=1);


  extern function void          register                (ovm_object_wrapper obj);



  //-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_

  // name-based static methods - deprecated

  extern static function void          set_type_override (string original_type_name,
                                                         string override_type_name,
                                                         bit    replace=1);

  extern static function void          set_inst_override(string full_inst_path,
                                                         string original_type_name,
                                                         string override_type_name);

  extern static function ovm_object    create_object    (string requested_type_name,  
                                                         string parent_inst_path="",
                                                         string name="");

  extern static function ovm_component create_component (string requested_type_name,
                                                         string parent_inst_path="",
                                                         string name, 
                                                         ovm_component parent);


  extern static function void          print_override_info(string requested_type_name,
                                                         string parent_inst_path="",
                                                         string name="");

  extern static function void          print_all_overrides(int all_types=0);

  extern static function void          auto_register    (ovm_object_wrapper obj);


  //----------------------------------------------------------------------------
  // PRIVATE MEMBERS
  
  extern protected function void  m_debug_create        (string requested_type_name,
                                                         ovm_object_wrapper requested_type,
                                                         string parent_inst_path,
                                                         string name);
  
  extern protected function void  m_debug_display       (string requested_type_name,
                                                         ovm_object_wrapper result,
                                                         string full_inst_path);
  static local ovm_factory m_inst;

  protected bit                  m_types[ovm_object_wrapper];
  protected bit                  m_lookup_strs[string];
  protected ovm_object_wrapper   m_type_names[string];

  protected ovm_factory_override m_type_overrides[$];
  protected ovm_factory_override m_inst_overrides[$];

  local ovm_factory_override     m_override_info[$];
  local static bit m_debug_pass;

endclass


// our singleton factory; it is initialized upon first call to ovm_factory::get

`const ovm_factory factory = ovm_factory::get();



`endif // OVM_FACTORY_SVH

