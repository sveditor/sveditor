// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_report_server.svh#16 $
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

`ifndef OVM_REPORT_SERVER_SVH
`define OVM_REPORT_SERVER_SVH

typedef class ovm_report_object;

//----------------------------------------------------------------------
// CLASS ovm_report_server
//----------------------------------------------------------------------
class ovm_report_server;

  local int max_quit_count; 
  local int quit_count;
  local int severity_count[ovm_severity];
  local int id_count[string];

  bit enable_report_id_count_summary=1;

  function new();
    set_max_quit_count(0);
    reset_quit_count();
    reset_severity_counts();
  endfunction

  //--------------------------------------------------------------------
  // accessors for setting, getting, and incrementing
  // the various counts
  //--------------------------------------------------------------------
  function int get_max_quit_count();
    return max_quit_count;
  endfunction

  function void set_max_quit_count(int count);
    max_quit_count = count < 0 ? 0 : count;
  endfunction

  function void reset_quit_count();
    quit_count = 0;
  endfunction

  function void incr_quit_count();
    quit_count++;
  endfunction

  function int get_quit_count();
    return quit_count;
  endfunction

  function void set_quit_count(int quit_count);
    quit_count = quit_count < 0 ? 0 : quit_count;
  endfunction

  function bit is_quit_count_reached();
    return (quit_count >= max_quit_count);
  endfunction

  function void reset_severity_counts();
    ovm_severity_type s;

    s = s.first();
    forever begin
      severity_count[s] = 0;
      if(s == s.last()) break;
      s = s.next();
    end

  endfunction

  function void set_severity_count(ovm_severity severity, int count);
    severity_count[severity] = count < 0 ? 0 : count;
  endfunction

  function int get_severity_count(ovm_severity severity);
    return severity_count[severity];
  endfunction

  function void incr_severity_count(ovm_severity severity);
    severity_count[severity]++;
  endfunction

  function void copy_severity_counts(ovm_report_server dst);
    foreach(severity_count[s]) begin
      dst.set_severity_count(s,severity_count[s]);
    end
  endfunction

  function void set_id_count(string id, int count);
    id_count[id] = count < 0 ? 0 : count;
  endfunction

  function int get_id_count(string id);
    if(id_count.exists(id))
      return id_count[id];
    return 0;
  endfunction

  function void incr_id_count(string id);
    if(id_count.exists(id))
      id_count[id]++;
    else
      id_count[id] = 1;
  endfunction

  function void copy_id_counts(ovm_report_server dst);
    foreach(id_count[s]) begin
      dst.set_id_count(s,id_count[s]);
    end
  endfunction

  //--------------------------------------------------------------------
  // f_display
  //--------------------------------------------------------------------
  function void f_display(OVM_FILE file, string str);
    if (file == 0)
      $display(str);
    else
      $fdisplay(file, str);
  endfunction

  //--------------------------------------------------------------------
  // report
  //--------------------------------------------------------------------
  extern virtual function void report(
      ovm_severity severity,
      string name,
      string id,
      string message,
      int verbosity_level,
      string filename,
      int line,
      ovm_report_object client
      );
  //--------------------------------------------------------------------
  // process_report
  //--------------------------------------------------------------------
  extern virtual function void process_report(
      ovm_severity severity,
      string name,
      string id,
      string message,
      ovm_action action,
      OVM_FILE file,
      string filename,
      int line,
      string composed_message,
      int verbosity_level,
      ovm_report_object client
      );
  //--------------------------------------------------------------------
  // compose_message
  //--------------------------------------------------------------------
  extern virtual function string compose_message(
      ovm_severity severity,
      string name,
      string id,
      string message,
      string filename,
      int    line
      );
  //--------------------------------------------------------------------
  // summarize
  //
  // summarize prints out report statistics to the standard
  // output
  //--------------------------------------------------------------------

  function void summarize(OVM_FILE file=0);
    string id;
    string name;
    string output_str;

    f_display(file, "");
    f_display(file, "--- OVM Report Summary ---");
    f_display(file, "");

    if(max_quit_count != 0) begin
      if ( quit_count >= max_quit_count ) f_display(file, "Quit count reached!");
      $sformat(output_str, "Quit count : %d of %d",
                             quit_count, max_quit_count);
      f_display(file, output_str);
    end

    f_display(file, "** Report counts by severity");
    for(ovm_severity_type s = s.first(); 1; s = s.next()) begin
      if(severity_count.exists(s)) begin
        int cnt;
        cnt = severity_count[s];
        name = s.name();
        $sformat(output_str, "%s :%5d", name, cnt);
        f_display(file, output_str);
      end
      if(s == s.last()) break;
    end

    if (enable_report_id_count_summary) begin

      f_display(file, "** Report counts by id");
      for(int found = id_count.first(id);
           found;
           found = id_count.next(id)) begin
        int cnt;
        cnt = id_count[id];
        $sformat(output_str, "[%s] %5d", id, cnt);
        f_display(file, output_str);
      end

    end

  endfunction

  //--------------------------------------------------------------------
  // dump_server_state
  //--------------------------------------------------------------------
  function void dump_server_state();

    string s;
    ovm_severity_type sev;
    string id;

    f_display(0, "report server state");
    f_display(0, "");   
    f_display(0, "+-------------+");
    f_display(0, "|   counts    |");
    f_display(0, "+-------------+");
    f_display(0, "");

    $sformat(s, "max quit count = %5d", max_quit_count);
    f_display(0, s);
    $sformat(s, "quit count = %5d", quit_count);
    f_display(0, s);

    sev = sev.first();
    forever begin
      int cnt;
      cnt = severity_count[sev];
      s = sev.name();
      $sformat(s, "%s :%5d", s, cnt);
      f_display(0, s);
      if(sev == sev.last())
        break;
      sev = sev.next();
    end

    if(id_count.first(id))
    do begin
      int cnt;
      cnt = id_count[id];
      $sformat(s, "%s :%5d", id, cnt);
      f_display(0, s);
    end
    while (id_count.next(id));

  endfunction

endclass

`include "base/ovm_report_handler.svh"

//----------------------------------------------------------------------
// CLASS ovm_report_global_server
//
// Singleton object that maintains a single global report server
//----------------------------------------------------------------------
class ovm_report_global_server;

  static ovm_report_server global_report_server = null;

  function new();
    if (global_report_server == null)
      global_report_server = new;
  endfunction

  function ovm_report_server get_server();
    return global_report_server;
  endfunction

  function void set_server(ovm_report_server server);
    server.set_max_quit_count(global_report_server.get_max_quit_count());
    server.set_quit_count(global_report_server.get_quit_count());
    global_report_server.copy_severity_counts(server);
    global_report_server.copy_id_counts(server);
    global_report_server = server;
  endfunction

endclass

`endif // OVM_REPORT_SERVER_SVH
