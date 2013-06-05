
// This file defines macros that the next package references
`define PKG1_MACRO1 class
`define PKG1_MACRO2 endclass

package pkg1;
	`include "pkg1_cls1.svh"
	`include "pkg1_cls2.svh"
endpackage