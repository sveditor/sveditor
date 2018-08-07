/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.open_decl;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestOpenModIfc extends SVCoreTestCaseBase {
	
	public void testOpenModuleDecl() {
		String doc =
			"module m1;\n" +
			"	wire A, B;\n" +
			"endmodule\n" +
			"\n" +
			"module m2;\n" +
			"	<<MARK>>m1 u1();\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 1, "m1", SVDBItemType.ModuleDecl);
	}

	public void testOpenInterfaceDecl() {
		String doc =
			"interface m1;\n" +
			"	wire A, B;\n" +
			"endinterface\n" +
			"\n" +
			"interface m2;\n" +
			"	<<MARK>>m1 u1();\n" +
			"endinterface\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 1, "m1", SVDBItemType.InterfaceDecl);
	}

	/** NOTE: this cannot be tested with the current StringBIDITextScanner()
	 * 
	 */
	public void disabled_testOpenModuleDeclwPreComment() {
		String doc =
			"module a(output o, input i);\n" +		// 1
			"	assign o = i;\n" +
			"endmodule\n" +
			"\n" +					
			"module b(output o, input i);\n" +		// 5
			"	// a.\n" +
			"	<<MARK>>a a0(o, i);\n" +					// 7
			"endmodule\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 1, "a", SVDBItemType.ModuleDecl);
	}

	public void testStructFieldModuleScope() {
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct packed {\n" + 			// 5
			"	logic [ 3:0] bbbb;\n" + 
			"} MyStruct;\n" +
			"\n" +
			"module m;\n" +
			"\n" +									// 10
			"initial begin\n" +
			"	MyStruct mystruct_obj;\n" +
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", mystruct_obj.b<<MARK>>bbb, myclass_obj.aaaa);\n" +	 // 14
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "bbbb", SVDBItemType.VarDeclItem);
	}

	public void testUnionFieldModuleScope() {
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef union {\n" + 			// 5
			"	logic [ 3:0] aaaa;\n" + 
			"	logic [ 3:0] bbbb;\n" + 
			"} MyUnion;\n" +
			"\n" +
			"module m;\n" +							// 10
			"\n" +									
			"initial begin\n" +
			"	MyUnion myunion_obj;\n" +
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", myunion_obj.b<<MARK>>bbb, myclass_obj.aaaa);\n" +	 // 15
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "bbbb", SVDBItemType.VarDeclItem);
	}

	public void testStructUnionFieldModuleScope() {
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" + 			// 5
			"	union {\n" +
			"		logic [ 3:0] aaaa;\n" + 
			"		logic [ 3:0] bbbb;\n" +
			"	} u;\n" +
			"} MyStruct;\n" +						// 10
			"\n" +
			"module m;\n" +
			"\n" +									
			"initial begin\n" +
			"	MyStruct mystruct_obj;\n" +			// 15
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", mystruct_obj.u.bb<<MARK>>bb, myclass_obj.aaaa);\n" +	 // 17
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "bbbb", SVDBItemType.VarDeclItem);
	}
	
	public void testClassFieldModuleScope() {
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct packed {\n" + 			// 5
			"	logic [ 3:0] bbbb;\n" + 
			"} MyStruct;\n" +
			"\n" +
			"module m;\n" +
			"\n" +									// 10
			"initial begin\n" +
			"	MyStruct mystruct_obj;\n" +
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", mystruct_obj.bbbb, myclass_obj.a<<MARK>>aaa);\n" +	 // 14
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "aaaa", SVDBItemType.VarDeclItem);
	}

	public void testModulePort() {
		String doc = 
			"module m(\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"\n" +							// 5	
			"	always @(posedge cl<<MARK>>k_i) begin\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "clk_i", SVDBItemType.VarDeclItem);
	}
	
	public void testModulePort_2() {
		String doc = 
			"module m(\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"\n" +							// 5	
			"	always @(posedge clk_i) begin\n" +
			"		r<<MARK>>st_n <= 0;\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "rst_n", SVDBItemType.VarDeclItem);
	}	
	
	public void testModuleParameter() {
		String doc = 
			"module m #(parameter int P1=1, parameter int P2=2) (\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"\n" +							// 5	
			"	initial begin\n" +
			"		repeat (<<MARK>>P1) begin\n" +
			"		end\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "P1", SVDBItemType.ModIfcClassParam);
	}	

	public void testModuleParameter_1() {
		String doc = 
			"module m (\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"	parameter P1=1;\n" +							// 5	
			"	parameter P2=1;\n" +							// 6	
			"	initial begin\n" +
			"		repeat (<<MARK>>P1) begin\n" +
			"		end\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "P1", SVDBItemType.VarDeclItem);
	}
	
	public void testOpenModuleTypeWithInstanceSameName() {
		String doc =
			"module foo (\n" + // 1
			"	input a,\n" +
			"	output b\n" +
			");\n" +
			"\n" +
			"	assign a = b;\n" +
			"endmodule\n" +
			"\n" +
			"module foo_test;\n" +
			"	// Open declaration works\n" + // 10
			"	foo foo1\n" +
			"	(\n" +
			"		.a(),\n" +
			"		.b()\n" +
			"	);\n" +
			"\n" +
			"	// Does not work\n" +
			"	f<<MARK>>oo foo\n" +				// 18
			"	(\n" +
			"		.a(),\n" +
			"		.b()\n" +
			"	);\n" +
			"endmodule\n" 
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "foo", SVDBItemType.ModuleDecl);
	}
	
	public void testOpenMacroRootedTaskPathDecl() {
		String doc =
			"`define TOP m2\n" + // 1
			"module s1;\n" +
			"	task t1;\n" +
			"	endtask\n" +
			"endmodule\n" +
			"module m1;\n" +
			"	s1		s1_i();\n" +
			"endmodule\n" +
			"\n" +
			"module m2;\n" + // 10
			"	m1		m1_i();\n" +
			"endmodule\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		`TOP.m1_i.s1_i.t<<MARK>>1();\n" + // 15
			"	end\n" +
			"endmodule\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		OpenDeclTests.runTest(this, doc, 0, "t1", SVDBItemType.Task);
	}	
}

