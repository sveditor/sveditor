// $Id: //dvt/vtech/dev/main/ovm/src/base/ovm_component.svh#43 $
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

`ifndef OVM_COMPONENT_SVH
`define OVM_COMPONENT_SVH

typedef class ovm_config_setting;      
typedef class ovm_phase;
typedef class ovm_event_pool;
typedef class ovm_object;
typedef class ovm_transaction;
typedef class ovm_printer;
typedef class ovm_root;

//------------------------------------------------------------------------------
//
// CLASS: ovm_component
//
//------------------------------------------------------------------------------
// Root base class for structural elements. Provides name and hiearchy
// information about the object.
//------------------------------------------------------------------------------

virtual class ovm_component extends ovm_report_object;

  //----------------------------------------------------------------------------
  // Constructor
  //----------------------------------------------------------------------------
  // When creating a new component, you must always provide a local "instance",
  // or "leaf" name. You must also provide a handle to the component's parent,
  // unless the component is a top-level component (i.e. it is created in a
  // static component such as a module or interface).
  //----------------------------------------------------------------------------

    extern  function new (string name, ovm_component parent);

  //----------------------------------------------------------------------------
  // Hierarchy
  //----------------------------------------------------------------------------
  // These methods provide user access to information about the component
  // hierarchy.
  // 
  // - Children info can be obtained via get_first_child, get_next_child,
  //   and get_child methods. These operate like the built-in methods to the
  //   associative array data-type. 
  //
  // - The set_name method overrides the one in ovm_object so that name change
  //   can be reflected in the component hierarchy: The parent's children list
  //   must be updated, and the children's full names must now incorporate this
  //   component's new name.
  //
  // - The lookup method can be used to find a component having the given
  //   hierarchical path. If the path begins with a '.', then it is taken to
  //   be an absolute path. Else, the given path is relative to this component.
  //----------------------------------------------------------------------------

    extern virtual function ovm_component get_parent       ();
    extern virtual function string        get_full_name    ();
    extern function ovm_component         get_child        (string name);
    extern function int                   get_first_child  (ref string name);
    extern function int                   get_next_child   (ref string name);
    extern function int                   get_num_children ();
    extern function int                   has_child        (string name);
    extern virtual function void          set_name         (string name);
    extern function ovm_component         lookup           (string name );

    /*protected*/ ovm_component m_parent;
    protected ovm_component m_children[string];

  //----------------------------------------------------------------------------
  // Phases
  //----------------------------------------------------------------------------
  // Components execute their behavior in strictly ordered, pre-defined phases.
  // Each phase is defined by its own method, which derived components can
  // override to incorporate component-specific behavior. During simulation,
  // the phases are executed one by one, where one phase must complete before
  // the next phase begins. The following brieft describe each phase:
  //
  // new
  //     Also known as the constructor, the component does basic initialization
  //     of any members not subject to configuration.
  //
  // build
  //     The component constructs its children. It uses get_config
  //     interface to obtain any configuration for itself, the set_config
  //     interface to set any configuration for its own children, and the
  //     factory interface for actually creating the children and other
  //     objects it might need.
  // 
  // connect
  //     The component now makes connections (binds TLM ports and exports)
  //     from child-to-child or from child-to-self (i.e. to promote a child
  //     port or export up the hierarchy for external access. Afterward,
  //     all connections are checked via resolve_bindings before entering
  //     the end_of_elaboration phase. 
  //
  // end_of_elaboration
  //     At this point, the entire testbench environment has been built and
  //     connected. No new components and connections may be created from
  //     this point forward. Components can do final checks for proper
  //     connectivity, and it can initiate communication with other tools
  //     that require stable, quasi-static component structure..
  //
  // start_of_simulation
  //     The simulation is about to begin, and this phase can be used to
  //     perform any pre-run activity such as displaying banners, printing
  //     final testbench topology and configuration information.
  //
  // run
  //     This is where verification takes place. It is the only predefined,
  //     time-consuming phase. A component's primary function is implemented
  //     in the 'run' task. Other processes may be forked if desired. When
  //     a component returns from its run task, it does not signify completion
  //     of its run phase. Any processes that it may have forked CONTINUE TO
  //     RUN. The run phase terminates in one of three ways:
  //
  //     stop - When a component's enable_stop_interrupt bit is set and
  //            global_stop_request is called, the component's stop task
  //            is called. Components can implement stop to allow completion
  //            of in-progress transactions, flush queues, etc. Upon return
  //            from stop by all enabled components, a kill is issued.
  //
  //     kill - When called, all component's run processes are killed
  //            immediately. While kill can be called directly, it is
  //            recommended that components use the stopping mechanism.
  //            This affords a more ordered and safe shut-down.
  //
  //     timeout - If a timeout was set, then the phase ends if it expires
  //            before either of the above occur. 
  //
  //     If none of the above occur, simulation can continue "forever", or
  //     the simulator may end simulation prematurely if it determines that
  //     all processes are waiting
  //
  // extract
  //     This phase can be used to extract simulation results from coverage
  //     collectors and scoreboards, collect status/error counts, statistics,
  //     and other information from components in bottom-up order. Being a
  //     separate phase, extract ensures all relevant data from potentially
  //     independent sources (i.e. other components) are collected before
  //     being checked in the next phase.
  //
  // check
  //     Having extracted vital simulation results in the previous phase,
  //     the check phase can be used to validate such data and determine
  //     the overall simulation outcome. It too executes bottom-up.
  //
  // report
  //     Finally, the report phase is used to output results to files and/or
  //     the screen. 
  //
  // All task-based phases (run is the only pre-defined task phase) will run
  // forever until killed or stopped via do_kill_all or global_stop_request.
  // The latter causes the component's stop() method to get called back if
  // the enable_stop_interrupt bit is set. After all components' stop() tasks
  // return, the OVM will call do_kill_all to end the phase.
  //
  // The kill method kills all processes spawned by this component in this
  // task-based phase. The do_kill_all method recursively calls kill() on
  // all its children.
  //
  // The flush method can be overridden in derived components to flush queues
  // and other such cleanup. The do_flush method will recursively call flush
  // on the entire sub-tree bottom up.
  //
  // The do_func_phase and do_task_phase methods are hooks for calling all of
  // the phases. By default, they merely invoke the appropriate phase method.
  // The component may override this for any pre or post phase activities.
  //
  // A components build phase callback is not called if m_build_done is set.
  // You must set this build if you calls build directly, else build will be
  // called again. 
  //
  // Note: the post_new, export_connections, import_connections, and pre_run
  // phases are deprecated. build replaces post_new, connections replace both
  // import_ and export_connections, and start_of_simulation replaces pre_run.
  //
  //----------------------------------------------------------------------------

    extern virtual  function void  build   ();
    extern virtual  function void  connect ();
    extern virtual  function void  end_of_elaboration ();
    extern virtual  function void  start_of_simulation ();
    extern virtual  task           run     ();
    extern virtual  function void  extract ();
    extern virtual  function void  check   ();
    extern virtual  function void  report  ();

    // process control for task-based phases, e.g. 'run'
    extern virtual  task           suspend ();
    extern virtual  task           resume  ();
    extern virtual  task           restart ();
    extern function string         status  ();
    extern virtual  function void  kill    ();

    extern virtual  function void  resolve_bindings ();
    extern virtual  function void  flush   ();

    extern virtual  task           stop (string ph_name);

    extern virtual  function void  do_func_phase (ovm_phase phase);
    extern virtual  task           do_task_phase (ovm_phase phase);

    extern virtual  function void  do_kill_all ();
    extern          function void  do_resolve_bindings ();
    extern          function void  do_flush();

    ovm_phase m_curr_phase=null;
    protected int enable_stop_interrupt = 0;

    protected bit m_build_done=0;

  //----------------------------------------------------------------------------
  // Configuration
  //----------------------------------------------------------------------------
  // Components can be designed to be user-configurable in terms of its
  // topology (the kind and number of children it has), mode of operation, and
  // run-time parameters (knobs). The configuration interface accommodates
  // this common need, allowing component composition and state to be modified
  // without having to derive new classes and new class hierarchies for
  // every configuration scenario. 
  //
  //
  // set_config_*
  //   Calling set_config_* causes configuration settings to be created and
  //   placed in a table internal to this component. There are similar global
  //   methods that store settings in a global table. Each setting stores the
  //   supplied inst_name, field_name, and value for later use by descendent
  //   components during their construction. (The global table applies to
  //   all components.)
  //
  // get_config_*
  //   When a descendant component calls a get_config_* method, the inst_name
  //   and field_name provided in the get call are matched against all the
  //   configuration settings stored in the global table and then in each
  //   component in the parent hierarchy, top-down. Upon the first match,
  //   the value stored in the configuration setting is returned. Thus,
  //   precedence is global, following by the top-level component, and so on
  //   down to the descendent component's parent. If a get_config_* all
  //   succeeds in finding a setting for the given inst_name and field_name,
  //   the output value is assigned the value from the original set_config_*
  //   call and 1 returned, else 0 is returned.
  //
  //   The clone bit clones the data inbound. The get_config_object method can
  //   also clone the data outbound.
  //
  // apply_config_settings
  //   Searches for all config settings matching this component's instance path.
  //   For each match, the appropriate set_*_local method is called using the
  //   matching config setting's field_name and value. Provided the set_*_local
  //   method is implemented, the component property associated with the
  //   field_name is assigned the given value. 
  //
  // print_config_settings
  //   Used for debugging configuration settings, this routine prints the list
  //   of settings that apply to this component. The settings are printing in
  //   the order of their precedence.  A null comp argument causes this
  //   component's settings to be printed. An empty field argument means show
  //   all matches for this component, i.e. all fields.  The recurse argument
  //   indicate to print config from comp (or this component) and below.
  //
  // static bit print_config_matches
  //   Setting this static variable causes get_config_* to print info about
  //   matching configuration settings as they are being applied.
  //
  // REVIEW: print_config_matches should work with apply_config_settings as well
  //         should not be in ovm_component? What if in ovm_root as non-static?
  //----------------------------------------------------------------------------

    extern virtual function void set_config_int    (string inst_name,  
                                                    string field_name,
                                                    ovm_bitstream_t value);


    extern virtual function void set_config_object (string inst_name,  
                                                    string field_name,
                                                    ovm_object value,  
                                                    bit clone=1);

    extern virtual function void set_config_string (string inst_name,  
                                                    string field_name,
                                                    string value);

    extern virtual function bit  get_config_int    (string field_name,
                                                   inout ovm_bitstream_t value);

    extern virtual function bit  get_config_object (string field_name,
                                                    inout ovm_object value,  
                                                    input bit clone=1);

    extern virtual function bit  get_config_string (string field_name,
                                                    inout string value);

    extern virtual function void apply_config_settings (bit verbose=0);

    extern         function void print_config_settings (string field="", 
                                                    ovm_component comp=null, 
                                                    bit recurse=0);
    static bit print_config_matches = 0; 
    protected ovm_config_setting m_configuration_table[$];
 

  //----------------------------------------------------------------------------
  // Factory
  //----------------------------------------------------------------------------
  // The factory interface provides components convenient access to the OVM's
  // central ovm_factory object. The create_*, set_*, and print_override_info
  // methods call the corresponding method in ovm_factory, passing what
  // arguments it can to reduce the number of arguments required of the user.
  //
  // create_component
  // create_object
  //
  // set_type_override
  // set_type_override_by_type
  //
  // set_inst_override
  // set_inst_override_by_type
  //
  // print_override_info
  //   Calls ovm_factory::print_override_info, providing this components full
  //   name as the parent_inst_path. 
  //
  // create/clone
  //   The create and clone methods from the ovm_object base class are disabled
  //   for components. Components are instead created via the ovm_factory.
  //----------------------------------------------------------------------------


    extern function ovm_component create_component (string requested_type_name, 
                                                    string name);

    extern function ovm_object    create_object    (string requested_type_name,
                                                    string name="");

    extern static function void   set_type_override_by_type
                                                   (ovm_object_wrapper original_type, 
                                                    ovm_object_wrapper override_type,
                                                    bit replace=1);

    extern function void          set_inst_override_by_type(string relative_inst_path,  
                                                    ovm_object_wrapper original_type,
                                                    ovm_object_wrapper override_type);

    extern static function void   set_type_override(string original_type_name, 
                                                    string override_type_name,
                                                    bit    replace=1);

    extern function void          set_inst_override(string relative_inst_path,  
                                                    string original_type_name,
                                                    string override_type_name);

    extern function void          print_override_info(string requested_type_name,
                                                    string name="");

    // overridden to disable
    extern virtual function ovm_object create (string name=""); 
    extern virtual function ovm_object clone  ();


  //----------------------------------------------------------------------------
  // Hierarchical Reporting
  //----------------------------------------------------------------------------
  // This interface provides versions of the set_report_* methods in
  // the ovm_report_object base class that are applied recursively
  // to this component and all its children.
  //
  // set_report_*_action_hier
  //   These methods recursively associate the specified action
  //   with reports of the given severity, id, or severity-id pair. An
  //   action associated with a particular severity-id pair takes
  //   precedence over an action associated with id, which take
  //   precedence over an an action associated with a severity.
  // 
  // set_report_*_file_hier
  //   These methods recursively associate the specified FILE
  //   descriptor with reports of the given severity, id, or severity-id
  //   pair.  A FILE associated with a particular severity-id pair takes
  //   precedence over a FILE associated with id, which take precedence
  //   over an a FILE associated with a severity, which takes precedence
  //   over the default FILE descriptor.
  //
  // set_report_verbosity_level_hier
  //   This method recursively sets the maximum verbosity
  //   level for reports for this component and all those below it.
  //   Any report from this component subtree whose verbosity exceeds
  //   this maximum will be ignored.
  // 
  // When a report is issued and its associated action has the LOG bit
  // set, the report will be sent to its associated FILE descriptor.
  //----------------------------------------------------------------------------

    extern function void set_report_severity_action_hier (ovm_severity severity,
                                                          ovm_action action);

    extern function void set_report_id_action_hier       (string id,
                                                          ovm_action action);

    extern function void set_report_severity_id_action_hier(ovm_severity severity,
                                                          string id,
                                                          ovm_action action);

    extern function void set_report_default_file_hier    (OVM_FILE file);

    extern function void set_report_severity_file_hier   (ovm_severity severity,
                                                          OVM_FILE file);

    extern function void set_report_id_file_hier         (string id,
                                                          OVM_FILE file);

    extern function void set_report_severity_id_file_hier(ovm_severity severity,
                                                          string id,
                                                          OVM_FILE file);

    extern function void set_report_verbosity_level_hier (int verbosity);
  

  //----------------------------------------------------------------------------
  // Recording
  //----------------------------------------------------------------------------
  // These methods comprise the component-based transaction recording
  // interface. The methods can be used to record the transactions that
  // this component "sees", i.e. produces or consumes.
  //
  // NOTE: The API and implementation are subject to change once a
  //       vendor-independent use-model is determined.
  //----------------------------------------------------------------------------

    extern protected 
                 function integer m_begin_tr (ovm_transaction tr,
                                              integer parent_handle=0,
                                              bit    has_parent=0,
                                              string stream_name="main",
                                              string label="",
                                              string desc="",
                                              time begin_time=0);

    extern       function void    accept_tr  (ovm_transaction tr,
                                              time accept_time=0);

    extern       function integer begin_tr   (ovm_transaction tr,
                                              string stream_name="main",
                                              string label="",
                                              string desc="",
                                              time begin_time=0);

    extern       function integer begin_child_tr (ovm_transaction tr,
                                              integer parent_handle=0,
                                              string stream_name="main",
                                              string label="",
                                              string desc="",
                                              time begin_time=0);

    extern       function void    end_tr     (ovm_transaction tr,
                                              time end_time=0,
                                              bit free_handle=1);

    extern       function integer record_error_tr
                                             (string stream_name="main",
                                              ovm_object info=null,
                                              string label="error_tr",
                                              string desc="",
                                              time   error_time=0,
                                              bit    keep_active=0);

    extern       function integer record_event_tr
                                             (string stream_name="main",
                                              ovm_object info=null,
                                              string label="event_tr",
                                              string desc="",
                                              time   event_time=0,
                                              bit    keep_active=0);
    extern virtual protected 
                 function void    do_accept_tr(ovm_transaction tr);

    extern virtual protected 
                 function void    do_begin_tr(ovm_transaction tr,
                                              string stream_name,
                                              integer tr_handle);

    extern virtual protected 
                 function void    do_end_tr  (ovm_transaction tr,
                                              integer tr_handle);

    protected ovm_event_pool event_pool;


  //----------------------------------------------------------------------------
  //                     PRIVATE or PSUEDO-PRIVATE members
  //                      *** Do not call directly ***
  //         Implementation and even existence are subject to change. 
  //----------------------------------------------------------------------------
  // Most local methods are prefixed with m_, indicating they are not
  // user-level methods. SystemVerilog does not support friend classes,
  // which forces some otherwise internal methods to be exposed (i.e. not
  // be protected via 'local' keyword). These methods are also prefixed
  // with m_ to indicate they are not intended for public use.
  //
  // Internal methods will not be documented, although their implementa-
  // tions are freely available via the open-source license.
  //----------------------------------------------------------------------------

    extern virtual local function void m_set_full_name ();

    extern local function void m_extract_name(string name ,
                                              output string leaf ,
                                              output string remainder );
    local integer m_stream_handle[string];
    local integer m_tr_h[ovm_transaction];

    extern virtual function bit m_add_child (ovm_component child);

    `ifndef INCA
    protected process m_phase_process;
    `endif
    protected event m_kill_request;

    string m_name;

    bit print_enabled = 1;

  //----------------------------------------------------------------------------
  //                          DEPRECATED MEMBERS
  //                      *** Do not use in new code ***
  //                  Convert existing code when appropriate.
  //----------------------------------------------------------------------------
  // Deprecated static methods:
  // 
  // global_stop_request
  //   replaced by ovm_top.stop_request
  //
  // Deprecated phases:
  //
  // post_new
  //   replaced by build (top-down)
  //
  // import/export_connections
  //   Consolidated into the connect phase; deferred binding enforcement
  //   via resolve_bindings allows connections to be order-independent
  //
  // pre_run
  //   replaced by start_of_simulation
  //----------------------------------------------------------------------------

    extern static  function  void  global_stop_request();

    extern virtual function  void  post_new ();
    extern virtual function  void  import_connections ();
    extern virtual function  void  configure ();
    extern virtual function  void  export_connections ();
    extern virtual function  void  pre_run (); 

    extern static  function ovm_component find_component   (string comp_match);
    extern static  function void          find_components  (string comp_match, 
                                                    ref ovm_component comps[$]);
    extern static  function ovm_component get_component    (int ele);
    extern static  function int           get_num_components ();

    `include "compatibility/urm_message_compatibility.svh"

endclass : ovm_component

// for backward compatibility
typedef ovm_component ovm_threaded_component;

            
`endif // OVM_COMPONENT_SVH

