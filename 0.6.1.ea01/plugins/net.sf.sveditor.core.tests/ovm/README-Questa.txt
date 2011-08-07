Open Verification Methodology
Questa-specifc Topics

Installing the OVM Kit
-----------------------

Installation of the OVM kit requires only unpacking the kit in a
convenient location.  No additional installation procedures or scripts
are necessary.

Running the examples
--------------------

The scripts included with the OVM kit package require that you have
ModelSim or Questa version 6.3 or later installed (see the Questa
compatibility table below) and that the commands vlib, vcom, vlog, and
vsim are in your command search path.

The simplest way to run an example is to cd to the example directory of
your choice and execute the run_questa.doc file.

  % cd ovm/examples/tlm/tlm_fifo
  % ./run_questa

The "run_questa" scripts execute the following commands

  % vlib work
  % vlog -f compile_questa_sv.f
  % vsim -do vsim.do

Each compile_questa_sv.f file contains all the command line options
necessary to compile each example.

Using the OVM Library
---------------------

You can make the OVM library accessible by your SystemVerilog program by
using either the package technique or the include technique.  To use
packages import ovm_pkg. If you are using the sequence and field
automation macros you will also need to include the macro
defintions. E.g.

import ovm_pkg::*;
`include "ovm_macros.svh"

To use the include technique you include a single file:

`include "ovm.svh"

You will need to put the location of the OVM source as a include
directory in your compilation command line.

For example:

vlog +incdir+$OVM_HOME/src $OVM_HOME/src/ovm_pkg.sv

where $OVM_HOME is set to the root of your ovm installation.

OVM and Questa Compatibility
----------------------------

Various versions of OVM have been tested on various version of Questa.
The table below matches OVM versions and Questa versions

+-------------+------------------------------+
| OVM Version |  Questa Version              |
+-------------+------------------------------+
| 1.0         | 6.3d                         |
+-------------+------------------------------+
| 1.0.1       | 6.3d, 6.3e                   |
+-------------+------------------------------+
| 1.1         | 6.3.d, 6.3e                  |
+-------------+------------------------------+
| 2.0         | 6.3h, 6.4                    |
+-------------+------------------------------+
| 2.0.1       | 6.3{i,j}, 6.4, 6.4{a,b}      |
+-------------+------------------------------+
| 2.0.2       | 6.4{d,e}, 6.5, 6.5{a,b}      |
+-------------+------------------------------+
| 2.0.3       | 6.4{d,e,f}, 6.5, 6.5{a,b,c}  |
+-------------+------------------------------+

Note: Questa-6.3x provides limited support for the type-based
factory. The two examples which use type-based factory are
examples/factory and examples/hello_world.  Contact your Mentor
technical representative for more details.

----------------------------------------------------------------------
