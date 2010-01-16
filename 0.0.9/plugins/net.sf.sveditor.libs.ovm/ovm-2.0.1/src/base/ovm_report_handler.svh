// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_report_handler.svh#22 $
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

`ifndef OVM_REPORT_HANDLER_SVH
`define OVM_REPORT_HANDLER_SVH

typedef class ovm_report_object;
typedef class ovm_report_server;
typedef class ovm_report_global_server;

`ifdef INCA

    class ovm_hash #(type T=int, I1=int, I2=int);
      local T d[string];
      function void set(I1 i1, I2 i2, T t);
        string s;
        $swrite(s,i1,":",i2);
        d[s] = t;
      endfunction
      function T get(I1 i1,I2 i2);
        string s;
        $swrite(s,i1,":",i2);
        return d[s];
      endfunction
      function int exists(I1 i1, I2 i2);
        string s;
        if(d.num() == 0) return 0;
        $swrite(s,i1,":",i2);
        return d.exists(s);
      endfunction
      function int first(string index);
        return d.first(index);
      endfunction
      function int next(string index);
        return d.next(index);
      endfunction
      function T fetch(string index);
        return d[index];
      endfunction
    endclass : ovm_hash
`endif
   
//----------------------------------------------------------------------
// CLASS ovm_report_handler
//----------------------------------------------------------------------
class ovm_report_handler;

  ovm_report_global_server m_glob;

  // This is the maximum verbosity level for this report
  // handler.  If any report has a higher verbosity level,
  // it is simply ignored

  int m_max_verbosity_level;

  // actions : severity, id, (severity,id)
  ovm_action severity_actions[ovm_severity];
  `ifndef INCA
    id_actions_array id_actions;
    id_actions_array severity_id_actions[ovm_severity];

    // file handles : default, severity, action, (severity,id)
    OVM_FILE default_file_handle;
    OVM_FILE severity_file_handles[ovm_severity];
    id_file_array id_file_handles;
    id_file_array severity_id_file_handles[ovm_severity];
  `endif
  `ifdef INCA
    ovm_action id_actions[string];
    ovm_hash #(ovm_action,ovm_severity,string) severity_id_actions = new;

    OVM_FILE default_file_handle;
    OVM_FILE severity_file_handles[ovm_severity];
    OVM_FILE id_file_handles[string];
    ovm_hash #(OVM_FILE,ovm_severity,string) severity_id_file_handles = new;
  `endif

  function new();
    m_glob = new();
    initialize;
  endfunction

  function ovm_report_server get_server();
    return m_glob.get_server();
  endfunction

  // forward the call to the server
  function void set_max_quit_count(int max_count);
    ovm_report_server srvr;
    srvr = m_glob.get_server();
    srvr.set_max_quit_count(max_count);
  endfunction

  function void summarize(OVM_FILE file = 0);
    ovm_report_server srvr;
    srvr = m_glob.get_server();
    srvr.summarize(file);
  endfunction

  function void report_header(OVM_FILE file = 0);

    ovm_report_server srvr;

    srvr = m_glob.get_server();
    srvr.f_display(file, "----------------------------------------------------------------");
    srvr.f_display(file, ovm_revision_string());
    srvr.f_display(file, ovm_mgc_copyright);
    srvr.f_display(file, ovm_cdn_copyright);
    srvr.f_display(file, "----------------------------------------------------------------");
  endfunction

  //--------------------------------------------------------------------
  // initialize
  // UPDATE COMMENTS
  // all severities both DISPLAY and LOG each report. In
  // addition, ERRORs are also COUNTED (so the simulation
  // will terminate when max_quit_count is reached) FATALs
  // also EXIT (ie, the simulation is immediately
  // terminated)
  //
  // All files (default, severity, id and (severity,id))
  // are initially set to zero. This means that they will be
  // ignored.
  //--------------------------------------------------------------------

  function void initialize();
    set_default_file(0);
    m_max_verbosity_level = OVM_MEDIUM;
    set_defaults();
  endfunction

  //--------------------------------------------------------------------
  // run_hooks
  //
  // run the report hooks
  //--------------------------------------------------------------------
  virtual function bit run_hooks(ovm_report_object client,
                                 ovm_severity severity,
                                 string id,
                                 string message,
                                 int verbosity,
                                 string filename,
                                 int line);

    bit ok;

    ok = client.report_hook(id, message, verbosity, filename, line);

    case(severity)
      OVM_INFO:     ok &= client.report_info_hook   (id, message, verbosity, filename, line);
      OVM_WARNING:  ok &= client.report_warning_hook(id, message, verbosity, filename, line);
      OVM_ERROR:    ok &= client.report_error_hook  (id, message, verbosity, filename, line);
      OVM_FATAL:    ok &= client.report_fatal_hook  (id, message, verbosity, filename, line);
    endcase

    return ok;

  endfunction

  //--------------------------------------------------------------------
  // get_severity_id_file
  //
  // Return the file id based on the severity and the id
  //--------------------------------------------------------------------
  local function OVM_FILE get_severity_id_file(ovm_severity severity, string id);

   `ifndef INCA
    id_file_array array;

    if(severity_id_file_handles.exists(severity)) begin
      array = severity_id_file_handles[severity];      
      if(array.exists(id))
        return array[id];
    end
   `else
    if (severity_id_file_handles.exists(severity,id))
      return severity_id_file_handles.get(severity,id);
   `endif


    if(id_file_handles.exists(id))
      return id_file_handles[id];

    if(severity_file_handles.exists(severity))
      return severity_file_handles[severity];

    return default_file_handle;

  endfunction

  //--------------------------------------------------------------------
  // set_verbosity_level
  //
  // sets the maximum verbosity level
  // for this report handler. All reports of higher
  // verbosity will be ignored
  //--------------------------------------------------------------------
  function void set_verbosity_level(int verbosity_level);
    m_max_verbosity_level = verbosity_level;
  endfunction

  //--------------------------------------------------------------------
  // get_verbosity_level
  //--------------------------------------------------------------------
  function int get_verbosity_level();
    return m_max_verbosity_level;
  endfunction

  //--------------------------------------------------------------------
  // get_action
  //
  // Retrieve the action based on severity and id.  First,
  // look to see if there is an action associated with the
  // (severity,id) pair.  Second, look to see if there is an
  // action associated with the id.  If neither of those has
  // an action then return the action associated with the
  // severity.
  //--------------------------------------------------------------------
  function ovm_action get_action(ovm_severity severity, string id);

   `ifndef INCA
    id_actions_array array;

    if(severity_id_actions.exists(severity)) begin
      array = severity_id_actions[severity];
      if(array.exists(id))
        return array[id];
    end
   `else
    if (severity_id_actions.exists(severity,id))
      return severity_id_actions.get(severity,id);
   `endif

    if(id_actions.exists(id))
      return id_actions[id];

    return severity_actions[severity];

  endfunction

  //--------------------------------------------------------------------
  // get_file_handle
  //
  // Retrieve the file handle associated with the severity
  // and id. First, look to see if there is a file handle
  // associated with the (severity,id) pair.  Second, look
  // to see if there is a file handle associated with the
  // id.  If neither the (severity,id) pair nor the id has
  // an associated action then return the action associated
  // with the severity.
  //--------------------------------------------------------------------
  function OVM_FILE get_file_handle(ovm_severity severity, string id);
    OVM_FILE file;
  
    file = get_severity_id_file(severity, id);
    if (file != 0)
      return file;
  
    if (id_file_handles.exists(id)) begin
      file = id_file_handles[id];
      if (file != 0)
        return file;
    end

    if (severity_file_handles.exists(severity)) begin
      file = severity_file_handles[severity];
      if(file != 0)
        return file;
    end

    return default_file_handle;
  endfunction

  //--------------------------------------------------------------------
  // report
  //
  // add line and file info later ...
  //
  // this is the public access report function. It is not
  // visible to the user but is accessed via
  // ovm_report_info, ovm_report_warning,
  // ovm_report_error and ovm_report_fatal.
  //--------------------------------------------------------------------
  virtual function void report(
      ovm_severity severity,
      string name,
      string id,
      string message,
      int verbosity_level,
      string filename,
      int line,
      ovm_report_object client
      );
 
    ovm_report_server srvr;
    srvr = m_glob.get_server();
    srvr.report(severity,name,id,message,verbosity_level,filename,line,client);
    
  endfunction

  //--------------------------------------------------------------------
  // format_action
  //--------------------------------------------------------------------
  function string format_action(ovm_action action);
    string s;

    if(action == OVM_NO_ACTION) begin
      s = "NO ACTION";
    end
    else begin
      s = "";
      if(action & OVM_DISPLAY)   s = {s, "DISPLAY "};
      if(action & OVM_LOG)       s = {s, "LOG "};
      if(action & OVM_COUNT)     s = {s, "COUNT "};
      if(action & OVM_EXIT)      s = {s, "EXIT "};
      if(action & OVM_CALL_HOOK) s = {s, "CALL_HOOK "};
      if(action & OVM_STOP)      s = {s, "STOP "};
    end

    return s;
  endfunction

  function void set_severity_action(input ovm_severity severity,
                                    input ovm_action action);
    severity_actions[severity] = action;
  endfunction

  function void set_defaults();
    set_severity_action(OVM_INFO,    OVM_DISPLAY);
    set_severity_action(OVM_WARNING, OVM_DISPLAY);
    set_severity_action(OVM_ERROR,   OVM_DISPLAY | OVM_COUNT);
    set_severity_action(OVM_FATAL,   OVM_DISPLAY | OVM_EXIT);

    set_severity_file(OVM_INFO, default_file_handle);
    set_severity_file(OVM_WARNING, default_file_handle);
    set_severity_file(OVM_ERROR,   default_file_handle);
    set_severity_file(OVM_FATAL,   default_file_handle);
  endfunction

  function void set_id_action(input string id, input ovm_action action);
    id_actions[id] = action;
  endfunction

  function void set_severity_id_action(ovm_severity severity,
                                       string id,
                                       ovm_action action);
    `ifndef INCA
    severity_id_actions[severity][id] = action;
    `else
    severity_id_actions.set(severity,id,action);
    `endif
  endfunction
  
  // set_default_file, set_severity_file, set_id_file and
  // set_severity_id_file associate verilog file descriptors
  // with different kinds of reports in this report
  // handler. It is the users responsbility to open and
  // close these file descriptors correctly. Users may take
  // advantage of the fact that up to 32 files can be
  // described by the same file descriptor to send one
  // report to many files.
  //
  // set_default_file sets the default file associated with
  // any severity or id in this report handler.

  function void set_default_file(input OVM_FILE file);
    default_file_handle = file;
  endfunction

  // set_severity_file sets the file associated with a
  // severity in this report handler.  It is not visible to
  // the user but is accessed via ovm_set_severity_file. A
  // file associated with a severity overrides the default
  // file for this report handler.

  function void set_severity_file(input ovm_severity severity, input OVM_FILE file);
    severity_file_handles[severity] = file;
  endfunction

  // set_id_file sets the file associated with an id in this
  // report handler. It is not visible to the user but is
  // accessed via ovm_set_id_file. A file associated with an
  // id overrides the default file and any files associated
  // with a severity.

  function void set_id_file(input string id, input OVM_FILE file);
    id_file_handles[id] = file;
  endfunction

  // set_severity_id_file sets the file associated with a
  // (severity,id) pair. It is not visible to the user but
  // is accessed via ovm_set_severity_id_file. A file
  // associated with a (severity,id) pair overrides any
  // other file settings in this report handler

  function void set_severity_id_file(input ovm_severity severity,
                                      input string id,
                                      input OVM_FILE file);
  
    `ifndef INCA
    severity_id_file_handles[severity][id] = file;
    `else
    severity_id_file_handles.set(severity,id,file);
    `endif
  endfunction

  //--------------------------------------------------------------------
  // dump_state
  //--------------------------------------------------------------------
  function void dump_state();

    string s;
    ovm_severity_type severity;
    ovm_action a;
    string idx;
    OVM_FILE file;
    ovm_report_server srvr;
 
   `ifndef INCA
     id_actions_array id_a_ary;
     id_file_array id_f_ary;
   `else
     OVM_FILE id_f_ary[string];
   `endif

    srvr = m_glob.get_server();

    srvr.f_display(0, "----------------------------------------------------------------------");
    srvr.f_display(0, "report handler state dump");
    srvr.f_display(0, "");

    $sformat(s, "max verbosity level = %d", m_max_verbosity_level);
    srvr.f_display(0, s);

    //------------------------------------------------------------------
    // actions
    //------------------------------------------------------------------

    srvr.f_display(0, "");   
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "|   actions   |");
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "");   

    srvr.f_display(0, "*** actions by severity");
    foreach( severity_actions[severity] ) begin
      $sformat(s, "%s = %s", ovm_severity_type'(severity), format_action(severity_actions[severity]));
      srvr.f_display(0, s);
    end

    srvr.f_display(0, "");
    srvr.f_display(0, "*** actions by id");

    foreach( id_actions[idx] ) begin
      $sformat(s, "[%s] --> %s", idx, format_action(id_actions[idx]));
      srvr.f_display(0, s);
    end

    // actions by id

    srvr.f_display(0, "");
    srvr.f_display(0, "*** actions by id and severity");

    `ifndef INCA
    foreach( severity_id_actions[severity] ) begin
      // ADAM: is id_a_ary __copied__?
      id_a_ary = severity_id_actions[severity];
      foreach( id_a_ary[idx] ) begin
        $sformat(s, "%s:%s --> %s", ovm_severity_type'(severity), idx, format_action(id_a_ary[idx]));
        srvr.f_display(0, s);        
      end
    end
    `else
    begin
      string idx;
      if ( severity_id_actions.first( idx ) )
        do begin
            $sformat(s, "%s --> %s", idx,
              format_action(severity_id_actions.fetch(idx)));
            srvr.f_display(0, s);        
        end
        while ( severity_id_actions.next( idx ) );
    end
    `endif

    //------------------------------------------------------------------
    // Files
    //------------------------------------------------------------------

    srvr.f_display(0, "");
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "|    files    |");
    srvr.f_display(0, "+-------------+");
    srvr.f_display(0, "");   

    $sformat(s, "default file handle = %d", default_file_handle);
    srvr.f_display(0, s);

    srvr.f_display(0, "");
    srvr.f_display(0, "*** files by severity");
    foreach( severity_file_handles[severity] ) begin
      file = severity_file_handles[severity];
      $sformat(s, "%s = %d", ovm_severity_type'(severity), file);
      srvr.f_display(0, s);
    end

    srvr.f_display(0, "");
    srvr.f_display(0, "*** files by id");

    foreach ( id_file_handles[idx] ) begin
      file = id_file_handles[idx];
      $sformat(s, "id %s --> %d", idx, file);
      srvr.f_display(0, s);
    end

    srvr.f_display(0, "");
    srvr.f_display(0, "*** files by id and severity");

    `ifndef INCA
    foreach( severity_id_file_handles[severity] ) begin
      id_f_ary = severity_id_file_handles[severity];
      foreach ( id_f_ary[idx] ) begin
        $sformat(s, "%s:%s --> %d", ovm_severity_type'(severity), idx, id_f_ary[idx]);
        srvr.f_display(0, s);
      end
    end
    `else
    begin
      string idx;
      if ( severity_id_file_handles.first( idx ) )
        do begin
            $sformat(s, "%s --> %s", idx,
              format_action(severity_id_file_handles.fetch(idx)));
            srvr.f_display(0, s);        
        end
        while ( severity_id_file_handles.next( idx ) );
    end
    `endif

    srvr.dump_server_state();
    
    srvr.f_display(0, "----------------------------------------------------------------------");
  endfunction


endclass : ovm_report_handler

//----------------------------------------------------------------------
// CLASS default_report_server
//
// wrapper around ovm_report_global_server
//----------------------------------------------------------------------
class default_report_server;

  ovm_report_global_server glob;

  function new();
    glob = new;
  endfunction

  function ovm_report_server get_server();
    return glob.get_server();
  endfunction
  
endclass

`endif // OVM_REPORT_HANDLER_SVH
