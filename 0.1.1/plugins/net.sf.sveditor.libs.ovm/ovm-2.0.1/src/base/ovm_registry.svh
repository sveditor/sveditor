// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_registry.svh#14 $
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
`ifndef OVM_REGISTRY_SVH
`define OVM_REGISTRY_SVH

class ovm_component_registry #(type T=ovm_component, string Tname="<unknown>")
                                           extends ovm_object_wrapper;
  typedef ovm_component_registry #(T,Tname) this_type;

  function ovm_component create_component(string name, ovm_component parent);
    T obj;
//    obj = new(.name(name), .parent(parent));
    obj = new(name, parent);
    return obj;
  endfunction

  const static string type_name = Tname;

  function string get_type_name();
    return type_name;
  endfunction

  local static this_type me = get();

  static function this_type get();
    if (me == null) begin
      ovm_factory f = ovm_factory::get();
      me = new;
      f.register(me);
    end
    return me;
  endfunction

  static function T create(string name, ovm_component parent, string contxt="");
    ovm_object obj;
    ovm_factory f = ovm_factory::get();
    if (contxt == "" && parent != null)
      contxt = parent.get_full_name();
    obj = f.create_component_by_type(get(),contxt,name,parent);
    assert ($cast(create,obj))
    else $fatal(0,"Factory did not return a component of type '",type_name,"'. A component of type '",obj == null ? "null" : obj.get_type_name(),"' was returned instead. Name=",name," Parent=",parent==null?"null":parent.get_type_name()," contxt=",contxt);
  endfunction

  static function void set_type_override(ovm_object_wrapper override_type, bit replace=1);
    factory.set_type_override_by_type(get(),override_type,replace);
  endfunction

  static function void set_inst_override(ovm_object_wrapper override_type,
                                         string inst_path,
                                         ovm_component parent=null);
    string full_inst_path;
    if (parent != null) begin
      if (inst_path == "")
        inst_path = parent.get_full_name();
      else
        inst_path = {parent.get_full_name(),".",inst_path};
    end
    factory.set_inst_override_by_type(get(),override_type,inst_path);
  endfunction

endclass


class ovm_object_registry #(type T=ovm_object, string Tname="<unknown>")
                                           extends ovm_object_wrapper;
  typedef ovm_object_registry #(T,Tname) this_type;

  function ovm_object create_object(string name);
    T obj;
    obj = new();
    obj.set_name(name);
    return obj;
  endfunction

  const static string type_name = Tname;

  function string get_type_name();
    return type_name;
  endfunction

  local static this_type me = get();

  static function this_type get();
    if (me == null) begin
      ovm_factory f = ovm_factory::get();
      me = new;
      f.register(me);
    end
    return me;
  endfunction

  static function T create(string name="", ovm_component parent=null, string contxt="");
    ovm_object obj;
    ovm_factory f = ovm_factory::get();
    if (contxt == "" && parent != null)
      contxt = parent.get_full_name();
    obj = f.create_object_by_type(get(),contxt,name);
    assert ($cast(create,obj))
    else $fatal(0,"Factory did not return an object of type '",type_name,"'. An object of type '",obj == null ? "null" : obj.get_type_name(),"' was returned instead. Name=",name," Parent=",parent==null?"null":parent.get_type_name()," contxt=",contxt);
  endfunction

  static function void set_type_override(ovm_object_wrapper override_type, bit replace=1);
    factory.set_type_override_by_type(get(),override_type,replace);
  endfunction

  static function void set_inst_override(ovm_object_wrapper override_type,
                                         string inst_path,
                                         ovm_component parent=null);
    string full_inst_path;
    if (parent != null) begin
      if (inst_path == "")
        inst_path = parent.get_full_name();
      else
        inst_path = {parent.get_full_name(),".",inst_path};
    end
    factory.set_inst_override_by_type(get(),override_type,inst_path);
  endfunction

endclass

`endif
