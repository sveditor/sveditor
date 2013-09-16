Open Verification Methodology
version 2.0.3

(C) Copyright 2007-2009 Mentor Graphics Corporation
(C) Copyright 2007-2009 Cadence Design Systems, Incorporated
All Rights Reserved Worldwide

The OVM kit is licensed under the Apache-2.0 license.  The full text of
the licese is provided in this kit in the file LICENSE.txt

Installing the kit
------------------

Installation of OVM requires only unpacking the kit in a convenient
location.  No additional installation procedures or scripts are
necessary.

Using the OVM
-------------

You can make the OVM library accessible by your SystemVerilog program by
using either the package technique or the include technique.  To use
packages import ovm_pkg. If you are using the field automation macros
you will also need to include the macro defintions. E.g.

import ovm_pkg::*;
`include "ovm_macros.svh"

To use the include technique you include a single file:

`include "ovm.svh"

You will need to put the location of the OVM source as a include
directory in your compilation command line.

------------------------------------------------------------------------


