
// Ensures macros propagate top-down
package pkg1;
	`define PKG1_MACRO1 class
	`include "pkg1_cls1.svh"
	`define PKG1_MACRO2 endclass
	`include "pkg1_cls2.svh"
endpackage