/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltinNet;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.stmt.SVDBParamPort;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseModuleBodyItems extends TestCase {
	
	public void testPackageModule() {
		String content =
			"package p;\r\n" +
		    "typedef enum logic[1:0] {\r\n" +
		    "    e0, e1, e2, e3\r    } e;" +
			"endpackage\r\n" +
			"\r\n" +
			"module t1\r\n" +
			"	(\r\n" +
		    "    input e [1:0] eee // No parse error.\r    );\r\n" +
		    "endmodule\r\n"
		    ;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testPackageModule");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "p", "t1");
	}

	public void testDelayedAssign() {
		String content =
			"module t;\n" +
			"	logic a;\n" +
			"	assign #1 a = 1; // Error.\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testDelayedAssign");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t");
	}

	public void testDelayedExprAssign() {
		String content =
			"module t;\n" +
			"	logic a;\n" +
			"	assign #(1+2ps) a = 1; // Error.\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testDelayedAssign");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t");
	}
	
	public void testModuleSizedParameter() {
		String content = 
			"module t\n" +
			"#(\n" +
			"parameter [2:0] a = 2'b01\n" +
			");\n" +
			"endmodule\n";
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testModuleSizedParameter");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t");
	}

	public void testModuleGenvarDecl() {
		String content = 
			"module t4;\n" +
			"	genvar k;\n" +
			"endmodule\n";
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testModuleSizedParameter");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t4");
	}

	
	public void testModuleInterfacePort() {
		String content = 
			"module t2\n" +
			"(\n" +
			"interface a\n" +
			");\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(content, "testModuleInterfacePort");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t2");
	}
	
	public void testModuleBitArrayPort() {
		String content =
			"module t3\n" +
			"(\n" +
			"input [1:0][1:0] a\n" +
			");\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);

		SVDBFile file = SVDBTestUtils.parse(content, "testModuleInterfacePort");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t3");
	}
	
	public void testModuleSignedPort() {
		String content =
			"module t5\n" +
			"(\n" +
			"output signed a\n" +
			");\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testModuleSignedPort");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t5");
	}

	public void testModuleSizedSignedPort() {
		String content =
			"module t2\n" +
			"(\n" +
			"       input signed [1:0] a\n" +
			");\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testModuleSizedSignedPort");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t2");
	}

	public void testAssignInvert() {
		String doc = 
			"module t;\n" +
			"	logic a, b;\n" +
			"	assign a = ~b; // Error!\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testAssignInvert");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t");
	}
	
	public void testAssignSystemTask() {
		String doc =
			"module t2;\n" +
			"	logic a, b;\n" +
			"	assign a = $abs(1)+$abs(1); // Error!\n" +
			"endmodule\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testAssignSystemTask");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t2");
	}

	
	public void testInitialBlock() {
		String doc =
			"module top;\n" +
			"    int a;\n" +
			"\n" +
			"    initial begin\n" +
			"        int b;\n" +
			"        b = 5;\n" +
			"        a = 6;\n" +
			"        assert(a == 6);\n" +
			"    end\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testInitialBlock");
		
		SVDBModIfcClassDecl top = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		SVDBScopeItem initial = null;
		for (ISVDBItemBase it : top.getItems()) {
			if (it.getType() == SVDBItemType.InitialBlock) {
				initial = (SVDBScopeItem)it;
				break;
			}
		}
		
		assertNotNull("Failed to find initial block", initial);
	}
	
	public void testPortList() {
		String doc =
			"module top(a, b, c, d);\n" +		// 1
			"    input a;\n" +					// 2
			"    output b;\n" +					// 3
			"    input [7:0] c;\n" +			// 4
			"    output[11:0] d;\n" +			// 5
			"\n" +								// 6
			"    wire [12:0] bus;\n" +			// 7
			"\n" +								// 8
			"    always @ (a) begin\n" +		// 9
			"        b = ~a;\n" +				// 10
			"    end\n" +						// 11
			"\n" +								// 12
			"endmodule\n"						// 13
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testPortList");
		
		for (ISVDBItemBase it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
			}
		}

		SVDBModIfcClassDecl top = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		for (SVDBParamPort p : top.getPorts()) {
			System.out.println("Port: " + p.getVarList().get(0).getName());
		}

		ISVDBItemBase a=null, b=null, c=null, d=null, bus=null;
		for (ISVDBItemBase it : top.getItems()) {
			String name = SVDBItem.getName(it);
			System.out.println("[Item] " + it.getType() + " " + name);
			if (it.getType() == SVDBItemType.VarDeclStmt) {
				for (SVDBVarDeclItem vi : ((SVDBVarDeclStmt)it).getVarList()) {
					if (name.equals("a")) {
						a = vi;
					} else if (name.equals("b")) {
						b = vi;
					} else if (name.equals("c")) {
						c = vi;
					} else if (name.equals("d")) {
						d = vi;
					} else if (name.equals("bus")) {
						bus = vi;
					}
				}
			}
		}
		
		assertNotNull(a);
		assertNotNull(b);
		assertNotNull(c);
		assertNotNull(d);
		assertNotNull(bus);
		
		assertEquals("input", ((SVDBVarDeclStmt)a).getTypeName());
		assertEquals("input", ((SVDBVarDeclStmt)a).getTypeName());
		assertTrue((bus instanceof SVDBVarDeclStmt));
		SVDBVarDeclStmt v = (SVDBVarDeclStmt)bus;
		System.out.println("bus.type.class=" + v.getTypeInfo().getClass().getName());
		assertTrue((((SVDBVarDeclStmt)bus).getTypeInfo() instanceof SVDBTypeInfoBuiltinNet));
		SVDBTypeInfoBuiltinNet net_type = (SVDBTypeInfoBuiltinNet)((SVDBVarDeclStmt)bus).getTypeInfo();
		assertEquals("[12:0]", 
				((SVDBTypeInfoBuiltin)net_type.getTypeInfo()).getVectorDim());
	}
	
	public void testTypedPortList() {
		String doc =
			"typedef struct {\n" +
			"    int a;\n" +
			"    int b;\n" +
			"} foo_t;\n" +
			"\n" +
			"module top(\n" +
			"    input int    a,\n" +
			"    input foo_t  b,\n" +
			"    input bar[13:0]\n" +
			"    );\n" +
			"\n" +
			"    always @ (a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testTypedPortList");
		
		for (ISVDBItemBase it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
			}
		}

		SVDBModIfcClassDecl top = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("top")) {
				top = (SVDBModIfcClassDecl)it;
				break;
			}
		}
		
		assertNotNull("Failed to find module top", top);

		SVDBVarDeclItem a=null, b=null, bar=null;
		for (SVDBParamPort p : top.getPorts()) {
			for (SVDBVarDeclItem pi : p.getVarList()) {
				System.out.println("Port: " + pi.getName());
				if (pi.getName().equals("a")) {
					a = pi;
				} else if (pi.getName().equals("b")) {
					b = pi;
				} else if (pi.getName().equals("bar")) {
					bar = pi;
				}
			}
		}
		
		assertNotNull(a);
		assertNotNull(b);
		assertNotNull(bar);

		assertEquals(SVDBDataType.UserDefined, b.getParent().getTypeInfo().getDataType());
		assertEquals("foo_t", ((SVDBTypeInfoUserDef)b.getParent().getTypeInfo()).getName());
	}

	public void testAlwaysBlock() {
		String doc =
			"module top;\n" +
			"\n" +
			"    always @ (posedge a) begin\n" +
			"        b = ~a;\n" +
			"    end\n" +
			"\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testAlwaysBlock");
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		for (ISVDBItemBase it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				System.out.println("Marker: " + ((SVDBMarkerItem)it).getMessage());
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR)) {
					errors.add(m);
				}
			}
		}

		SVDBTestUtils.assertFileHasElements(file, "top");
		
		assertEquals("No Errors", 0, errors.size());
	}

	public void testNestedModule() {
		String doc =
			"module top;\n" +
			"\n" +
			"    module inner;\n" +
			"    	always @ (posedge a) begin\n" +
			"       	 b = ~a;\n" +
			"    	end\n" +
			"    endmodule\n" +
			"\n" +
			"\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testAlwaysBlock");
		
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBModIfcClassDecl top = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("top")) {
				top = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module top", top);
		
		SVDBModIfcClassDecl inner = null;
		for (ISVDBItemBase it : top.getItems()) {
			if (SVDBItem.getName(it).equals("inner")) {
				inner = (SVDBModIfcClassDecl)it;
			}
		}

		assertNotNull("Failed to find module inner", inner);
	}
	
	public void testEmptyParamList() {
		String doc =
			"module t2\n" +
			"#(\n" +
			");\n" +
			"endmodule";

		SVDBFile file = SVDBTestUtils.parse(doc, "testAlwaysBlock");

		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "t2");
	}
	
	public void testParameterDeclaration() {
		
		String doc =
			"module t1;\n" +
			"    parameter c = 1;\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testParameterDeclaration");
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBModIfcClassDecl t1 = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("t1")) {
				t1 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t1", t1);
		
		SVDBParamPort c = null;
		for (ISVDBItemBase it : t1.getItems()) {
			if (SVDBItem.getName(it).equals("c")) {
				c = (SVDBParamPort)it;
			}
		}
		assertNotNull(c);
	}

	public void testParameterExprInit() {
		
		String doc =
			"module t;\n" +
			"    parameter a = 2;\n" +
			"    parameter b = a/2;\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testParameterExprInit");
		
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBModIfcClassDecl t = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("t")) {
				t = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t", t);
		
		SVDBParamPort a = null, b = null;
		for (ISVDBItemBase it : t.getItems()) {
			if (SVDBItem.getName(it).equals("a")) {
				a = (SVDBParamPort)it;
			} else if (SVDBItem.getName(it).equals("b")) {
				b = (SVDBParamPort)it;
			}
		}
		assertNotNull(a);
		assertNotNull(b);
	}

	public void testAlwaysVariants() {
		
		String doc =
			"module t3(input clock);\n" +
			"    always_ff@(posedge clock) begin\n" +
			"    end\n" +
			"    always_comb begin\n" +
			"    end\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testAlwaysVariants");
		SVDBTestUtils.assertNoErrWarn(file);
		
		SVDBModIfcClassDecl t3 = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("t3")) {
				t3 = (SVDBModIfcClassDecl)it;
			}
		}
		
		assertNotNull("Failed to find module t3", t3);
		
		// SVDBAlwaysBlock always_ff = null, always_comb = null;
		for (ISVDBItemBase it : t3.getItems()) {
			System.out.println("it: " + it.getType() + " " + SVDBItem.getName(it));
		}
	}

	// EXPECTED_ERROR: Generate blocks not currently supported
	public void testGenVars() {
		
		String doc =
			"module t4;\n" +
			"    for(genvar i=0; i<3; i++) begin\n" +
			"    end\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testGenVars");
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t4");
	}
	
	// Contains semantic error, in that both loops use the same index 
	public void testGen_LRM_Ex1() {
		String doc = 
			"module mod_a;\n" +
			"	genvar i;\n" +
			"	for (i=0; i<5; i=i+1) begin : a\n" +
			"		for (i=0; i<5; i=i+1) begin : b\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testGenVars");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "mod_a");
	}

	// Contains semantic error, in that both loops use the same index 
	public void testGen_LRM_Ex1_a() {
		String doc = 
			"module mod_a;\n" +
			"	genvar i;\n" +
			"	for (i=0; i<5; i=i+1) begin : a\n" +
			"		for (i=0; i<5; i=i+1) begin : b\n" +
			"		end\n" +
			"	end\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testGenVars");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "mod_a");
	}

	// Contains semantic error, in that logic 'a' and block 'a' conflict 
	public void testGen_LRM_Ex1_b() {
		String doc = 
			"module mod_b;\n" +
			"	genvar i;\n" +
			"	logic a;\n" +
			"	for (i=1; i<0; i=i+1) begin: a\n" +
			"	end\n" +
			"endmodule\n" 
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_Ex1_b");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "mod_b");
	}

	// error -- "a" conflicts with name of previous
	// loop even though indices are unique
	public void testGen_LRM_Ex1_c() {
		String doc = 
			"module mod_c;\n" +
			"	genvar i;\n" +
			"	for (i=1; i<5; i=i+1) begin: a\n" +
			"	end\n" +
			"	for (i=10; i<15; i=i+1) begin: a\n" +
			"	end\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_Ex1_c");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "mod_c");
	}

	public void testGen_LRM_Ex2() {
		String doc = 
			"module gray2bin1 (bin, gray);\n" +
			"	parameter SIZE = 8; // this module is parameterizable\n" +
			"	output [SIZE-1:0] bin;\n" +
			"	input [SIZE-1:0] gray;\n" +
			"	genvar i;\n" +
			"	generate\n" +
			"	for (i=0; i<SIZE; i=i+1) begin:bitnum\n" +
			"		assign bin[i] = ^gray[SIZE-1:i];\n" +
			"		// i refers to the implicitly defined localparam whose\n" +
			"		// value in each instance of the generate block is\n" +
			"		// the value of the genvar when it was elaborated.\n" +
			"	end\n" + // 12
			"	endgenerate\n" +
			"endmodule\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_Ex2");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "gray2bin1");
	}
	
	public void testGen_LRM_Ex3() {
		String doc = 
		"module addergen1 (co, sum, a, b, ci);\n" +
		"	parameter SIZE = 4;\n" +
		"	output [SIZE-1:0] sum;\n" +
		"	output co;\n" +
		"	input [SIZE-1:0] a, b;\n" +
		"	input ci;\n" +
		"	wire [SIZE :0] c;\n" +
		"	wire [SIZE-1:0] t [1:3];\n" +
		"	genvar i;\n" +
		"	assign c[0] = ci;\n" +
		"		// Hierarchical gate instance names are:\n" +
		"		// xor gates: bitnum[0].g1 bitnum[1].g1 bitnum[2].g1 bitnum[3].g1\n" +
		"		// bitnum[0].g2 bitnum[1].g2 bitnum[2].g2 bitnum[3].g2\n" +
		"		// and gates: bitnum[0].g3 bitnum[1].g3 bitnum[2].g3 bitnum[3].g3\n" +
		"		// bitnum[0].g4 bitnum[1].g4 bitnum[2].g4 bitnum[3].g4\n" +
		"		// or gates: bitnum[0].g5 bitnum[1].g5 bitnum[2].g5 bitnum[3].g5\n" +
		"		// Generated instances are connected with\n" +
		"		// multidimensional nets t[1][3:0] t[2][3:0] t[3][3:0]\n" +
		"		// (12 nets total)\n" +
		"	for(i=0; i<SIZE; i=i+1) begin:bitnum\n" +
		"		xor g1 ( t[1][i], a[i], b[i]);\n" +
		"		xor g2 ( sum[i], t[1][i], c[i]);\n" +
		"		and g3 ( t[2][i], a[i], b[i]);\n" +
		"		and g4 ( t[3][i], t[1][i], c[i]);\n" +
		"		or g5 ( c[i+1], t[2][i], t[3][i]);\n" +
		"	end\n" +
		"	assign co = c[SIZE];\n" +
		"endmodule\n"
		;
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_Ex3");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "addergen1");
	}

	public void testGen_LRM_Ex4() {
		String doc = 
			"module addergen1 (co, sum, a, b, ci);\n" +
			"	parameter SIZE = 4;\n" +
			"	output [SIZE-1:0] sum;\n" +
			"	output co;\n" +
			"	input [SIZE-1:0] a, b;\n" +
			"	input ci;\n" +
			"	wire [SIZE :0] c;\n" +
			"	genvar i;\n" +
			"	assign c[0] = ci;\n" +
			"	for(i=0; i<SIZE; i=i+1) begin:bitnum\n" +
			"		wire t1, t2, t3;\n" +
			"		xor g1 ( t1, a[i], b[i]);\n" +
			"		xor g2 ( sum[i], t1, c[i]);\n" +
			"		and g3 ( t2, a[i], b[i]);\n" +
			"		and g4 ( t3, t1, c[i]);\n" +
			"		or g5 ( c[i+1], t2, t3);\n" +
			"	end\n" +
			"	assign co = c[SIZE];\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_Ex4");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "addergen1");
	}

	public void testGen_LRM_Ex5() {
		String doc =
			"module ex5;\n" +
			"	parameter SIZE = 2;\n" +
			"	genvar i, j, k, m;\n" +
			"	generate\n" +
			"		for (i=0; i<SIZE; i=i+1) begin:B1 // scope B1[i]\n" +
			"			M1 N1(); // instantiates B1[i].N1\n" +
			"			for (j=0; j<SIZE; j=j+1) begin:B2 // scope B1[i].B2[j]\n" +
			"				M2 N2(); // instantiates B1[i].B2[j].N2\n" +
			"				for (k=0; k<SIZE; k=k+1) begin:B3 // scope B1[i].B2[j].B3[k]\n" +
			"					M3 N3(); // instantiates\n" +
			"				end // B1[i].B2[j].B3[k].N3\n" +
			"			end\n" +
			"			if (i>0) begin:B4 // scope B1[i].B4\n" +
			"				for (m=0; m<SIZE; m=m+1) begin:B5 // scope B1[i].B4.B5[m]\n" +
			"					M4 N4(); // instantiates\n" +
			"				end // B1[i].B4.B5[m].N4\n" +
			"			end\n" +
			"		end\n" +
			"	endgenerate\n" +
			"endmodule\n"
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_Ex5");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "ex5");
	}

	public void testGen_LRM_Ex_Cond_1() {
		String doc =
			"module test;\n" +
			"	parameter p = 0, q = 0;\n" +
			"	wire a, b, c;\n" +
			"	if (p == 1)\n" +
			"		if (q == 0)\n" +
			"			begin : u1 // If p==1 and q==0, then instantiate\n" +
			"				and g1(a, b, c); // AND with hierarchical name test.u1.g1\n" +
			"			end\n" +
			"		else if (q == 2)\n" +
			"			begin : u1 // If p==1 and q==2, then instantiate\n" + // 10
			"				or g1(a, b, c); // OR with hierarchical name test.u1.g1\n" +
			"			end\n" +
			"		else ; // If p==1 and q!=0 or 2, then no instantiation\n" +
			"	else if (p == 2)\n" + // 14
			"		case (q)\n" +
			"			0, 1, 2:\n" +
			"				begin : u1 // If p==2 and q==0,1, or 2, then instantiate\n" +
			"					xor g1(a, b, c); // XOR with hierarchical name test.u1.g1\n" + // 18 
			"				end\n" +
			"			default:\n" +
			"				begin : u1 // If p==2 and q!=0,1, or 2, then instantiate\n" +
			"					xnor g1(a, b, c); // XNOR with hierarchical name test.u1.g1\n" +
			"				end\n" +
			"		endcase\n" +
			"endmodule\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_ExCond_1");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "test");
	}

	public void testGen_LRM_Ex_Cond_2() {
		String doc =
			"module multiplier(a,b,product);\n" +
			"	parameter a_width = 8, b_width = 8;\n" +
			"	localparam product_width = a_width+b_width;\n" +
			"	input [a_width-1:0] a;\n" +
			"	input [b_width-1:0] b;\n" +
			"	output [product_width-1:0] product;\n" +
			"	generate\n" +
			"		if((a_width < 8) || (b_width < 8)) begin: mult\n" +
			"			CLA_multiplier #(a_width,b_width) u1(a, b, product);\n" +
			"		end\n" +
			"		else begin: mult\n" +
			"			WALLACE_multiplier #(a_width,b_width) u1(a, b, product);\n" +
			"		end\n" +
			"	endgenerate\n" +
			"endmodule\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testGen_LRM_ExCond_2");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "multiplier");
	}
	
	public void testClocking_LRM_Ex1() {
		String doc =
			"module test;\n" +
			"	clocking ck1 @(posedge clk);\n" +
			"		default input #1step output negedge;\n" +
			"	endclocking\n" +
			"endmodule\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testClocking_LRM_Ex1");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "test");
	}
	
	public void testClocking_DR() {
		String doc = 
			"interface control_if;\n" +
			"	clocking cb @(posedge clk);\n" +
			"	endclocking : cb\n" +
			"endinterface : control_if\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testClocking_DR");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "control_if");
	}

	public void testOutputPort() {
		
		String doc =
			"module t4(o);\n" +
			"    output logic o;\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testTypedInitializedParameterDecl");
		SVDBTestUtils.assertNoErrWarn(file);
		
		SVDBTestUtils.assertFileHasElements(file, "t4");
	}

	public void testUntypedInputPort() {
		
		String doc =
			"module t\n" +
			"(\n" +
			"output logic [3:0] out,\n" +
			"input logic [1:0] in,\n" +
			"input [1:0] in2\n" +
			");\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testUntypedInputPort");
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		SVDBModIfcClassDecl t = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("t")) {
				t = (SVDBModIfcClassDecl)it;
			}
		}
		assertNotNull("Failed to find module t", t);
		
		SVDBVarDeclItem out=null, in=null, in2=null;
		
		for (SVDBParamPort p : ((SVDBModIfcClassDecl)t).getPorts()) {
			for (SVDBVarDeclItem pi : p.getVarList()) {
				if (pi.getName().equals("out")) {
					out = pi;
				} else if (pi.getName().equals("in")) {
					in = pi;
				} else if (pi.getName().equals("in2")) {
					in2 = pi;
				}
			}
		}
		assertNotNull("Failed to find \"out\"", out);
		assertNotNull("Failed to find \"in\"", in);
		assertNotNull("Failed to find \"in2\"", in2);
	}

	public void testModportPort() {
		
		String doc =
			"module t2\n" +
			"(\n" +
			"AbcInterface.Mp mp\n" +
			");\n" +
			"	// Parsing incorrectly at the interface modport\n" +
			"endmodule\n";	

		SVDBFile file = SVDBTestUtils.parse(doc, "testModportPort");
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		SVDBModIfcClassDecl t2 = null;
		for (ISVDBItemBase it : file.getItems()) {
			if (SVDBItem.getName(it).equals("t2")) {
				t2 = (SVDBModIfcClassDecl)it;
			}
		}
		assertNotNull("Failed to find module t2", t2);
		
		SVDBVarDeclItem mp=null;
		
		for (SVDBParamPort p : ((SVDBModIfcClassDecl)t2).getPorts()) {
			for (SVDBVarDeclItem pi : p.getVarList()) {
				if (pi.getName().equals("mp")) {
					mp = pi;
				}
			}
		}
		assertNotNull("Failed to find \"mp\"", mp);
	}


	public void testTypedInitializedParameterDecl() {
		
		String doc =
			"module t3\n" +
			"#(\n" +
			"parameter int c [0:1] = '{0, 1}\n" +
			");\n" +
			"endmodule\n";			

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testTypedInitializedParameterDecl");
		
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t3");
	}

	public void testParameterArrayRefExpr() {
		
		String doc =
			"module t\n" +
			"#(\n" +
			"       parameter [1:0] a = 2'b10,\n" +
			"       parameter b = a[1]+1\n" +
			");\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testParameterArrayRefExpr");
		
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t");
	}

	public void testMappedParameterizedModule() {
		
		String doc =
			"module t5;\n" +
			"    Abc #(1, 2) abc(out, in);\n" +
			"    Abc #(.p(1), .p2(2)) abc2(out, in);\n" +
			"endmodule\n"
			;

		SVDBFile file = SVDBTestUtils.parse(doc, "testMappedParameterizedModule");
		
		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t5");
	}

	public void testGlobalParamRef() {
		
		String doc =
			"parameter int c [0:1] = '{0, 2};\n" +
			"	module t6\n" +
			"	#(\n" +
			"	parameter c2 = c[0]\n" +
			"	);\n" +
			"	endmodule\n"
			;
			
		SVDBFile file = SVDBTestUtils.parse(doc, "testMappedParameterizedModule");
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		SVDBTestUtils.assertFileHasElements(file, "t6");
	}


	public void testVarCompare() {
		String doc = 
			"module HalfSeTable(sIdx, LutIndex);\n" +
			"	// Optimize the table size by the sorting stage index.\n" +
			"	parameter sortId = 0;\n" +
			"	output logic [sortId*3-1:0] sIdx;\n" +
			"	input [2:0] LutIndex;\n" +
			"\n" +
			"	// Half SE table. Symbols are 802.11 Gray-encoded.\n" +
			"	always@(LutIndex) begin\n" +
			"		case(LutIndex)\n" +
			"    	// SE order:    (best)7   5   3   1  -1  -3  -5  -7\n" +
			"		3'b000: sIdx = (24'b100_101_111_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b001: sIdx = (24'b100_101_111_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b010: sIdx = (24'b101_100_111_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b011: sIdx = (24'b101_111_100_110_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b100: sIdx = (24'b111_101_110_100_010_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b101: sIdx = (24'b111_110_101_010_100_011_001_000)>>((8-sortId)*3);\n" +
			"		3'b110: sIdx = (24'b110_111_010_101_011_100_001_000)>>((8-sortId)*3);\n" +
			"		3'b111: sIdx = (24'b110_010_111_011_101_001_100_000)>>((8-sortId)*3);\n" +
			"		endcase\n" +
			"	end\n" +
			"endmodule\n";

		SVDBFile target_file = new SVDBFile("testMappedParameterizedModule");
		SVDBFile file = SVDBTestUtils.parse(doc, "testMappedParameterizedModule");
		
		SVDBFileMerger.merge(target_file, file, null, null, null);
		
		// Merge twice for good measure. The first time actually does something.
		// The second time ensures maximum compares
		SVDBFileMerger.merge(target_file, file, null, null, null);
		
		SVDBTestUtils.assertNoErrWarn(file);
		
		SVDBTestUtils.assertFileHasElements(file, "HalfSeTable");
	}
	
	public void testAlwaysIfElse() {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("testAlwaysIfElse",
				"module t;\n" +
				"	always@(posedge clk or negedge rst)\n" +
			    "	if(!rst)        state <= #1 grant0;\n" +
			    "	else            state <= #1 next_state;\n" +
				"endmodule\n",
				new String[] {"t"});
	}
	
	public void testAlwaysMultiLevelIf() {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("testAlwaysMultiLevelIf",
				"module t;\n" +
				"	always @(posedge clk)\n" +
				"		if(pri_out_tmp[7])      pri_out2 <= #1 3'h7;\n" +
				"		else\n" +
				"		if(pri_out_tmp[6])      pri_out2 <= #1 3'h6;\n" +
				"		else\n" +
				"		if(pri_out_tmp[5])      pri_out2 <= #1 3'h5;\n" +
				"		else\n" +
				"		if(pri_out_tmp[4])      pri_out2 <= #1 3'h4;\n" +
				"		else\n" +
				"		if(pri_out_tmp[3])      pri_out2 <= #1 3'h3;\n" +
				"		else\n" +
				"		if(pri_out_tmp[2])      pri_out2 <= #1 3'h2;\n" +
				"		else\n" +
				"		if(pri_out_tmp[1])      pri_out2 <= #1 3'h1;\n" +
				"		else                    pri_out2 <= #1 3'h0;\n" +
				"endmodule\n",
				new String[] {"t"});
	}
	
	public void testAlwaysCase() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module t;\n" +
			"	always @(pri_sel or pri_out0 or pri_out1 or  pri_out2)\n" +
			"		case(pri_sel)           // synopsys parallel_case full_case\n" +
			"			2'd0: pri_out = pri_out0;\n" +
			"			2'd1: pri_out = pri_out1;\n" +
			"			2'd2: pri_out = pri_out2;\n" +
			"		endcase\n" +
			"endmodule\n"
			;
		
		runTest("testAlwaysCase", doc, new String[] {"t"});
	}

	public void testTaskNonAnsiInputParam() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module t;\n" +
			"	task fill_mem;\n" +
			"		input           mode;\n" +
			"		integer         n, mode;\n" +
			"		begin\n" +
			"			for(n=0;n<(sz+1);n=n+1)\n" +
			"				begin\n" +
			"					case(mode)\n" +
			"						0:   mem[n] = { ~n[15:0], n[15:0] };\n" +
			"						1:   mem[n] = $random;\n" +
			"					endcase\n" +
			"				end\n" +
			"		end\n" +
			"	endtask\n" + 
			"endmodule\n"
			;

		runTest("testTaskNonAnsiInputParam", doc, new String[] {"t"});
	}

	public void testPreIncDec() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module t;\n" +
			"	int v;\n" +
			"\n" +
			"initial begin\n" +
			"	if (++v > 5) begin\n" +
			"		v = 2;\n" +
			"	end\n" +
			"\n" +
			"	if (--v < 2) begin\n" +
			"		v = 1;\n" +
			"	end\n" +
			"end\n" +
			"\n" +
			"endmodule\n"
			;

		runTest("testPreIncDec", doc, new String[] {"t"});
	}

	public void testPostIncDec() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module t;\n" +
			"	int v;\n" +
			"\n" +
			"initial begin\n" +
			"\n" +
			"	if (v++ > 1) begin\n" +
			"		v = 0;\n" +
			"	end\n" +
			"\n" +
			"	if (v-- == 0) begin\n" +
			"		v = 5;\n" +
			"	end\n" +
			"end\n" +
			"\n" +
			"endmodule\n"
			;

		runTest("testPostIncDec", doc, new String[] {"t"});
	}

	public void testMultiModuleInstantiation() {
		String doc = 
			"module t;\n" +
			"\n" +
			"	mod inst_1();\n" +
			"	mod inst_2();\n" +
			"\n" +
			"	mod inst_3(),\n" +
			"	inst_4();\n" +
			"\n" +
			"	assign a = 5;\n" +
			"\n" +
			"endmodule\n"
			;
		
		runTest("testMultiModuleInstantiation", doc, new String[] {"t"});
	}
	
	public void testVmmErrorBehaveBlock() {
		String doc = 
        "`define vmm_error(log, msg)  \\\n" +
        "do \\\n" +
        "	/* synopsys translate_off */ \\\n" +
        "	if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV, `__FILE__, `__LINE__)) begin \\\n" +
        "		void'(log.text(msg)); \\\n" +
        "		log.end_msg(); \\\n" +
        "	end \\\n" +
        "	/* synopsys translate_on */ \\\n" +
        "while (0)\n" +
        "\n" +
        "module t;\n" +
        "	initial begin\n" +
        "		repeat (10) begin\n" +
        "			if (!d.compare(d, diff)) begin\n" +
        "				`vmm_error(log, {\"Self comparison failed: \", diff});\n" +
        "			end\n" +
        "		end\n" +
        "	end\n" +
        "endmodule\n"
        ;
		
		runTest("", doc, new String[] {"t"});
	}
	
	public void testModulePreBodyImport() {
		String doc = 
			"package p;\n" +
			"endpackage\n" +
			"\n" +
			"module t import p::*; // Error.\n" +
			"	#()();\n" +
			"endmodule\n"
			;
		
		runTest("testModulePreBodyImport", doc, new String[] {"p", "t"});
	}

	public void testModulePreBodyImport2() {
		String doc = 
			"package p;\n" +
			"endpackage\n" +
			"\n" +
			"module t import p::*;\n" +
			"	#(\n" +
			"		parameter a = 0\n" +
			"	) // Error.\n" +
			"	();\n" +
			"endmodule\n" +
			"\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testModulePreBodyImport2", doc, new String[] {"p", "t", "p::*"});
	}

	public void testModulePreBodyImport3() {
		String doc = 
			"package p;\n" +
			"endpackage\n" +
			"\n" +
			"module t import p::*, p1::*, p2::*;\n" +
			"	#(\n" +
			"		parameter a = 0\n" +
			"	) // Error.\n" +
			"	();\n" +
			"endmodule\n" +
			"\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testModulePreBodyImport3", doc, new String[] {
				"p", "t", "p::*", "p1::*", "p2::*"});
	}
	
	public void testGatePrimitives1() {
		String doc = 
			"module gates();\n" +
			"	wire out0;\n" +
			"	wire out1;\n" +
			"	wire out2;\n" +
			"	reg  in1,in2,in3,in4;\n" +
			"\n" +
			"	not U1(out0,in1);\n" +
			"	and U2(out1,in1,in2,in3,in4);\n" +
			"	xor U3(out2,in1,in2,in3);\n" +

			"	initial begin\n" +
			"	$monitor(\n" +
			"	\"in1=%b in2=%b in3=%b in4=%b out0=%b out1=%b out2=%b\",\n" +
			"	in1,in2,in3,in4,out0,out1,out2);\n" + 
			"	in1 = 0;\n" +
			"	in2 = 0;\n" +
			"	in3 = 0;\n" +
			"	in4 = 0;\n" +
			"	#1 in1 = 1;\n" +
			"	#1 in2 = 1;\n" +
			"	#1 in3 = 1;\n" +
			"	#1 in4 = 1;\n" +
			"	#1 $finish;\n" + 
			"	end\n" +	
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		runTest("testGatePrimitives1", doc, new String[] {"gates"});
	}
	
	public void testGatePrimitives2() {
		String doc =
			"module switch_primitives();\n" +
			"\n" +
			"	wire  net1, net2, net3;\n" +
			"	wire  net4, net5, net6;\n" +
			"\n" +
			"	tranif0 my_gate1 (net1, net2, net3);\n" +
			"	rtranif1 my_gate2 (net4, net5, net6);\n" +
			"\n" +
			"endmodule\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		runTest("testGatePrimitives2", doc, new String[] {"switch_primitives"});
	}

	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}


}

