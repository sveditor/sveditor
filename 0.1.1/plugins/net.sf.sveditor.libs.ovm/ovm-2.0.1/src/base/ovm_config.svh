// $Id: ovm_config.svh,v 1.4 2008/08/29 11:06:49 jlrose Exp $
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

`ifndef OVM_CONFIG_SVH
`define OVM_CONFIG_SVH

typedef class ovm_component;


class ovm_config_setting;
  string inst;
  string field;
  string from;
  function new (string inst, string field, string from);
    this.inst = inst;
    this.field = field;
    this.from = from;
  endfunction
  virtual function string matches_string(ovm_component to, ovm_component from);
    string v;
    if(component_match(to)) begin
      if(from==null) begin
        v = " GLOBAL"; while(v.len() < 17) v = {v, " "};
      end
      else begin
        $swrite(v, " %0s(%0s)",from.get_full_name(), from.get_type_name()); while(v.len() < 17) v = {v, " "};
      end
      v = {v, " ", inst}; while(v.len() < 35) v = {v," "};
      v = {v, " ", field}; while(v.len() < 48) v = {v," "};
      return v;
    end
  endfunction
  virtual function string value_string();
    return "";
  endfunction
  virtual function string type_string();
    return "";
  endfunction
  function bit component_match (ovm_component to);
    if(to==null) return 0;
    return ovm_is_match(inst, to.get_full_name());
  endfunction
  function bit field_match (string to);
    if(to == "") return 0;
    return ovm_is_match(field, to);
  endfunction
  virtual function void print_match (ovm_component to, ovm_component from, string field);

    if((to!=null) && (from!=null))
      $display("Configuration match for %s.%s from %s: instance match = \"%s\"  field match = \"%s\"",
        to.get_full_name(), field, from.get_full_name(), inst, field);
    else if(to!=null)
      $display("Configuration match for %s.%s from %s: instance match = \"%s\"  field match = \"%s\"",
        to.get_full_name(), field, "GLOBAL", inst, field);
    else 
      $display("Configuration match for %s from %s: instance match = \"%s\"  field match = \"%s\"",
        field, "GLOBAL", inst, field);
  endfunction
endclass

class ovm_int_config_setting extends ovm_config_setting;
  ovm_bitstream_t value;
  function new (string inst, string field, ovm_bitstream_t value, string from);
    super.new(inst, field, from);
    this.value = value;
  endfunction
  virtual function string matches_string(ovm_component to, ovm_component from);
    if(component_match(to)) begin
      matches_string = super.matches_string(to, from);
      $swrite(matches_string, "%s int     %0d", matches_string, value);
    end
  endfunction
  virtual function string value_string();
    $sformat(value_string, "%0d", value);
  endfunction
  virtual function string type_string();
    return "int";
  endfunction
endclass

class ovm_string_config_setting extends ovm_config_setting;
  string value;
  function new (string inst, string field, string value, string from);
    super.new(inst, field, from);
    this.value = value;
  endfunction
  virtual function string matches_string(ovm_component to, ovm_component from);
    if(component_match(to)) begin
      matches_string = super.matches_string(to, from);
      $swrite(matches_string, "%s string  %0s", matches_string, value);
    end
  endfunction
  virtual function string value_string();
    value_string = value;
  endfunction
  virtual function string type_string();
    return "string";
  endfunction
endclass

class ovm_object_config_setting extends ovm_config_setting;
  ovm_object value;
  bit clone;
  function new (string inst, string field, ovm_object value, string from, bit clone);
    super.new(inst, field, from);
    this.value = value;
    this.clone = clone;
  endfunction
  virtual function string matches_string(ovm_component to, ovm_component from);
    string s2;
    if(component_match(to)) begin
      s2 = ovm_object_value_str(value);
      matches_string = super.matches_string(to, from);
      $swrite(matches_string, "%s %0s  %0s", matches_string, type_string(), s2);
    end
  endfunction
  virtual function string value_string();
    return ovm_object_value_str(value);
  endfunction
  virtual function string type_string();
    return {(value == null) ? "object" : value.get_type_name()};
  endfunction
endclass

//----------------------------------------------------------------------
//
// Global configuration
//
//----------------------------------------------------------------------

ovm_config_setting global_configuration_table [$];

// set_config_int
// --------------

function void  set_config_int    (string      inst_name,
                                                   string      field_name,
                                                   ovm_bitstream_t value);
  ovm_int_config_setting cfg;
  cfg = new(inst_name, field_name, value, "GLOBAL");
  global_configuration_table.push_front(cfg);
endfunction


// set_config_object
// -----------------

function void set_config_object  (string      inst_name,
                                                   string      field_name,
                                                   ovm_object  value,
                                                   bit         clone=1);
  ovm_object_config_setting cfg;
  if(clone && (value != null)) begin
    ovm_object tmp;
    tmp = value.clone();

    //If the user doesn't implement create, or attempts to clone an object that
    //doesn't allow cloning (such as a component reference) the clone will return null.
    if(tmp == null) begin
      ovm_component comp;
      if ($cast(comp,value)) begin
        ovm_report_error("INVCLNC", {"Clone failed during set_config_object ",
          "with an object that is an ovm_component. Components cannot be cloned."});
        return;
      end
      else begin
        ovm_report_warning("INVCLN", {"Clone failed during set_config_object, ",
          "the original reference will be used for configuration. Check that ",
          "the create method for the object type is defined properly."});
      end
    end
    else
      value = tmp;
  end

  cfg = new(inst_name, field_name, value, "GLOBAL", clone);
  global_configuration_table.push_front(cfg);
endfunction


// set_config_string
// -----------------

function void set_config_string  (string      inst_name,  
                                                   string      field_name,
                                                   string      value);
  ovm_string_config_setting cfg;
  cfg = new(inst_name, field_name, value, "GLOBAL");
  global_configuration_table.push_front(cfg);
endfunction


`endif // OVM_CONFIG_SVH
