// $Id: ovm_scoreboard.svh,v 1.7 2009/05/12 21:02:30 redelman Exp $
//-----------------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
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
//-----------------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// CLASS: ovm_scoreboard
//
// The ovm_scoreboard virtual class should be used as the base class for 
// user-defined scoreboards.
//
// Deriving from ovm_scoreboard will allow you to distinguish scoreboards from
// other component types inheriting directly from ovm_component. Such 
// scoreboards will automatically inherit and benefit from features that may be
// added to ovm_scoreboard in the future.
//------------------------------------------------------------------------------

virtual class ovm_scoreboard extends ovm_component;

  // Function: new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <ovm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, ovm_component parent);
    super.new(name, parent);
  endfunction

  const static string type_name = "ovm_scoreboard";

  virtual function string get_type_name ();
    return type_name;
  endfunction

endclass

