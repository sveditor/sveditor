// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_report_object.svh#24 $
//------------------------------------------------------------------------------
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
//------------------------------------------------------------------------------

`ifndef OVM_REPORT_CLIENT_SVH
`define OVM_REPORT_CLIENT_SVH

typedef class ovm_component;
typedef class ovm_env;
typedef class ovm_root;

//------------------------------------------------------------------------------
//
// CLASS: ovm_report_object
//
//------------------------------------------------------------------------------
//
// This class provides the public interface for reporting.  Any ovm_object-based
// object that wants to do reporting inherits from this class thus
// making available all the reporting methods.
//
// The ovm_report_object provides a front-end to a report handler, to which all
// operations are delegated and all state is maintained.  When a report passes
// through all filters, the report handler will forward the report to a central
// report server for final formatting and processing.
//
// Each report consists of an id string, severity, verbosity level, and the
// actual message.  If the verbosity level of a report is greater than the
// configured maximum verbosity level of its report handler, it is ignored.
//
// If a report passes the verbosity filter in effect, the handler will then
// determine the configured action, and, if the action includes output to a
// file, the configured file descriptor. 
//
//   Actions - can be set for (in increasing priority) severity, id, and
//   (severity,id) pair.  
//
//   File descriptors -- can be set for (in increasing priority) default,
//   severity level, an id, or a (severity,id) pair.  File descriptors are just
//   ordinary verilog file descriptors; they may refer to more than one file.
//   It is the user's responsibility to open and close them.
//
// File names and line numbers are not yet implemented.
//------------------------------------------------------------------------------

virtual class ovm_report_object extends ovm_object;

  ovm_report_handler m_rh;

  //----------------------------------------------------------------------------
  // Construction and management
  //----------------------------------------------------------------------------
  // new
  //   The constructor takes an optional name as argument. The name is used as
  //   the leaf name of the report object. This object's internal report-handler
  //   is then created. Most work is delegated to this report handler.
  //
  // get_report_handler
  //   Returns a handle to the underlying report handler.
  //
  // get_report_server
  //   Returns a handle to the common report server.
  //
  // set_report_handler
  //   Replaces this report object's existing report handler.
  //
  // reset_report_handler
  //   Resets the underlying report handler to its default settings. This clears
  //   any settings made with the set_report_* methods (see below).
  //
  // set_report_max_quit_count
  //   Sets the threshold at which the server will terminate simulation. When
  //   a report is issued and its action includes OVM_COUNT, an internal counter
  //   is incremented. When the max is reached, simulation is terminated via a
  //   call to 'die'.
  //
  // die
  //   This function is used by the report handler to trigger the end of
  //   simulation, or, if this report object is an ovm_component and we're
  //   in the run phase, the end of the run phase. 
  //
  //REVIEW: need way to plug-n-play a different server, e.g. set_server
  //REVIEW: propose to delete report_name member and methods in favor of
  //        get_full_name. Couple of source changes, and 2 tests need regold.
  //REVIEW: ovm_report_handler::initialize doesn't clear out id and (sev,id)
  //        arrays.
  //REVIEW: any discussion on reports-as-objects? This would reduce overrhead
  //        when forwarding arguments to various methods in handler, hooks, etc.
  //        A single container could be reused over and over because reporting
  //        does not consume time. It also may help to centralize message
  //        definition and formatting.
  //----------------------------------------------------------------------------

  function new(string name = "");
    super.new(name);
    m_rh = new();
  endfunction

  function ovm_report_handler get_report_handler();
    return m_rh;
  endfunction

  function ovm_report_server get_report_server();
    return m_rh.get_server();
  endfunction

  function void set_report_handler(ovm_report_handler handler);
    m_rh = handler;
  endfunction

  function void reset_report_handler;
    m_rh.initialize;
  endfunction

  function void set_report_max_quit_count(int max_count);
    m_rh.set_max_quit_count(max_count);
  endfunction

  virtual function void die();
    ovm_component comp;
    if($cast(comp, this) && run_ph.is_in_progress()) begin
      ovm_top.stop_request();
    end

    fork 
      begin
        //Fork allows die to complete on all threads before finishing
        report_summarize();
        $finish;
      end
    join_none

  endfunction


  //----------------------------------------------------------------------------
  // Core reporting methods
  //----------------------------------------------------------------------------
  // ovm_report_*
  //   These are the primary reporting methods in the OVM. Using these instead
  //   of $display and other ad hoc approaches ensures consistent output and
  //   central control over where output is directed and any actions that
  //   result. All reporting methods have the same arguments, albeit different
  //   default verbosities:
  //
  //   id        - a unique id for the report or report group that can be used
  //               for identification and targeted filtering.
  //
  //   message   - the message itself, preformatted
  //
  //   verbosity - the verbosity of the message. If this number is less than or
  //               equal to the effective verbosity level (see 
  //               set_report_verbosity_level), the report is issued. Each
  //               severity has a default verbosity level.
  //
  //   filename  - the filename in which the method was invoked.
  //
  //   line      - the line number of the file in which the method was invoked.
  //
  // These methods delegate to corresponding methods in the ovm_report_handler
  // associated with this report object, passing in the report_object's name and
  // handle, which defines the context of the report.
  //----------------------------------------------------------------------------

  virtual function void ovm_report_info( string id,
                                         string message,
                                         int verbosity = OVM_MEDIUM,
                                         string filename = "",
                                         int line = 0);
    m_rh.report(OVM_INFO, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction

  virtual function void ovm_report_warning( string id,
                                            string message,
                                            int verbosity = OVM_MEDIUM,
                                            string filename = "",
                                            int line = 0);
    m_rh.report(OVM_WARNING, get_full_name(), id, message, verbosity, 
               filename, line, this);
  endfunction

  virtual function void ovm_report_error( string id,
                                          string message,
                                          int verbosity = OVM_LOW,
                                          string filename = "",
                                          int line = 0);
    m_rh.report(OVM_ERROR, get_full_name(), id, message, verbosity, 
               filename, line, this);
  endfunction

  virtual function void ovm_report_fatal( string id,
                                          string message,
                                          int verbosity = OVM_NONE,
                                          string filename = "",
                                          int line = 0);
    m_rh.report(OVM_FATAL, get_full_name(), id, message, verbosity, 
               filename, line, this);
  endfunction

  virtual function void report_summarize(OVM_FILE file = 0);
    m_rh.summarize(file);
  endfunction

  virtual function void report_header(OVM_FILE file = 0);
    m_rh.report_header(file);
  endfunction

  //----------------------------------------------------------------------------
  // Report action hooks
  //----------------------------------------------------------------------------
  // These virtual methods offer subclasses the opportunity to perform
  // pre-report processing and filtering. First, the hook method associated with
  // the report's severity is called with the same arguments as given the report
  // report. If it returns 1, the catch-all method, report_hook, is then called.
  // If this method also returns 1, then the report is issued. If either hook
  // method returns 0, the report is not issued. If the severity-specific hook
  // returns 0, the catch-all hook is not called.  The default implementations
  // return 1, i.e. do not preempt reports from being issued.
  //----------------------------------------------------------------------------

  virtual function bit report_hook( string id,
                                    string message,
                                    int verbosity,
                                    string filename,
                                    int line);
    return 1;
  endfunction

  virtual function bit report_info_hook( string id,
                                         string message,
                                         int verbosity,
                                         string filename,
                                         int line);
    return 1;
  endfunction

  virtual function bit report_warning_hook( string id,
                                            string message,
                                            int verbosity,
                                            string filename,
                                            int line);
    return 1;
  endfunction

  virtual function bit report_error_hook( string id,
                                          string message,
                                          int verbosity,
                                          string filename,
                                          int line);
    return 1;
  endfunction

  virtual function bit report_fatal_hook( string id,
                                          string message,
                                          int verbosity,
                                          string filename,
                                          int line);
    return 1;
  endfunction


  //----------------------------------------------------------------------------
  // File and Action Configuration
  //----------------------------------------------------------------------------
  // set_report_*_action
  //   These methods associate the specified action
  //   with reports of the given severity, id, or severity-id pair. An action
  //   associated with a particular severity-id pair takes precedence over an
  //   action associated with id, which take precedence over an an action
  //   associated with a severity.
  // 
  // set_report_*_file
  //   These methods associate the specified FILE descriptor with reports of
  //   the given severity, id, or severity-id pair.  A FILE associated with a
  //   particular severity-id pair takes precedence over a FILE associated with
  //   id, which take precedence over an a FILE associated with a severity,
  //   which takes precedence over the default FILE descriptor.
  //
  // set_report_verbosity_level
  //   This method sets the maximum verbosity level for reports for this
  //   component and all those below it.  Any report from this component
  //   whose verbosity exceeds this maximum will be ignored.
  // 
  // When a report is issued and its associated action has the LOG bit
  // set, the report will be sent to its associated FILE descriptor.
  // The user is responsible for opening and closing these files.
  //----------------------------------------------------------------------------

  function void set_report_verbosity_level (int verbosity_level);
    m_rh.set_verbosity_level(verbosity_level);
  endfunction

  function void set_report_severity_action (ovm_severity severity, ovm_action action);
    m_rh.set_severity_action(severity, action);
  endfunction

  function void set_report_id_action (string id, ovm_action action);
    m_rh.set_id_action(id, action);
  endfunction

  function void set_report_severity_id_action (ovm_severity severity, string id,
                                               ovm_action action);
    m_rh.set_severity_id_action(severity, id, action);
  endfunction

  function void set_report_default_file ( OVM_FILE file);
    m_rh.set_default_file(file);
  endfunction

  function void set_report_severity_file (ovm_severity severity, OVM_FILE file);
    m_rh.set_severity_file(severity, file);
  endfunction

  function void set_report_id_file (string id, OVM_FILE file);
    m_rh.set_id_file(id, file);
  endfunction

  function void set_report_severity_id_file (ovm_severity severity, string id,
                                             OVM_FILE file);
    m_rh.set_severity_id_file(severity, id, file);
  endfunction

  function int get_report_verbosity_level();
    return m_rh.get_verbosity_level();
  endfunction

  function int get_report_action(ovm_severity severity, string id);
    return m_rh.get_action(severity,id);
  endfunction

  function int get_report_file_handle(ovm_severity severity, string id);
    return m_rh.get_file_handle(severity,id);
  endfunction

  function int ovm_report_enabled(int verbosity);
    return (get_report_verbosity_level() >= verbosity);
  endfunction

  function void dump_report_state();
    m_rh.dump_state();
  endfunction


  //----------------------------------------------------------------------------
  //                     PRIVATE or PSUEDO-PRIVATE members
  //                      *** Do not call directly ***
  //         Implementation and even existence are subject to change. 
  //----------------------------------------------------------------------------

  protected virtual function ovm_report_object m_get_report_object();
    return this;
  endfunction


  //----------------------------------------------------------------------------
  //                          DEPRECATED MEMBERS
  //                      *** Do not use in new code ***
  //                  Convert existing code when appropriate.
  //----------------------------------------------------------------------------

  function void avm_report_message( string id,
                                    string message,
                                    int verbosity = OVM_MEDIUM,
                                    string filename = "",
                                    int line = 0);
    m_rh.report(OVM_INFO, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction

  function void avm_report_warning( string id,
                                    string message,
                                    int verbosity = OVM_MEDIUM,
                                    string filename = "",
                                    int line = 0);
    m_rh.report(OVM_WARNING, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction

  function void avm_report_error( string id,
                                  string message,
                                  int verbosity = OVM_LOW,
                                  string filename = "",
                                  int line = 0);
    m_rh.report(OVM_ERROR, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction

  function void avm_report_fatal( string id,
                                  string message,
                                  int verbosity = OVM_NONE,
                                  string filename = "",
                                  int line = 0);
    m_rh.report(OVM_FATAL, get_full_name(), id, message, verbosity,
                filename, line, this);
  endfunction


endclass



//------------------------------------------------------------------------------
//
// CLASS: ovm_reporter
//
//------------------------------------------------------------------------------
// For use by objects that do not inherit the features of ovm_report_object,
// i.e. for use by non-ovm_component-based objects.
//------------------------------------------------------------------------------

class ovm_reporter extends ovm_report_object;

  const static string type_name = "ovm_reporter";

  function new(string name = "reporter");
    super.new(name);
  endfunction

  virtual function string get_type_name ();
    return type_name;
  endfunction

  virtual function ovm_object create (string name = "");
    ovm_reporter r; 
    if(name=="") name="reporter"; 
    r=new(name);
    return r;
  endfunction

endclass

`endif //OVM_REPORT_CLIENT_SVH
