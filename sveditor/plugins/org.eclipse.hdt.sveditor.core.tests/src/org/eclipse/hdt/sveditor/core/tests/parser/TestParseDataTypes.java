/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.parser;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseDataTypes extends TestCase {
	
	public void testWireLogicInputPort() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"`default_nettype none\n" +
				"module top(\n" +
				"	input wire logic rstb\n" +
				");\n" +
				"endmodule\n" +
				"`default_nettype wire\n"
			;
		
		ParserTests.runTestStrDoc(getName(), content, 
				new String[] {"top"});
	}

	public void testTypedefVirtual() throws SVParseException {
		LogHandle log = LogFactory.getLogHandle("testTypedefVirtual");
		String testname = "testTypedefVirtual";
		String content =
			"class foobar;\n" +
			"    typedef virtual my_if #(FOO, BAR, BAZ) my_if_t;\n" +
			"\n" +
			"endclass\n";
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"foobar", "my_if_t"});
		LogFactory.removeLogHandle(log);
	}
	
	public void testScopedTypeCast() throws SVParseException {
		String testname = "testScopedTypeCast";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foobar;\n" +
			"	function void f_func;\n" +
			"		int a = myscope::mytype'(5);\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		ParserTests.runTestStrDoc(testname, content, 
				new String[] {"foobar", "f_func"});
		LogFactory.removeLogHandle(log);
	}
	
	public void testSizedCast() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foobar;\n" +
			"	parameter FOO=5;\n" +
			"	function void f_func;\n" +
			"		int a, b;\n" +
			"		a = (FOO+1)'(b);\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		ParserTests.runTestStrDoc(getName(), content, 
				new String[] {"foobar", "f_func"});		
	}

	public void testTypedefEnumFwdDecl() throws SVParseException {
		String content =
			"class foo;\n" +
			"    typedef enum foo_enum_t;\n" +
			"    foo_enum_t        my_var;\n" +
			"endclass\n"
			;
		
		runTest(getName(), content,
				new String [] {"foo", "my_var"});
	}

	public void testSizedEnumVar() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foo;\n" +
			"    pkg_scope::my_type_e       mode_unsized;\n" +
			"    pkg_scope::my_type_e [4:1] mode_sized;\n" +
			"endclass\n"
			;
		
		runTest(getName(), content,
				new String [] {"foo", "mode_unsized", "mode_sized"});
	}
	
	public void testTypedefAnonymousFwdDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foo;\n" +
			"    typedef foo_enum_t;\n" +
			"    foo_enum_t        my_var;\n" +
			"endclass\n"
			;
		
		runTest("testTypedefEnumFwdDecl", content,
				new String [] {"foo", "my_var"});
	}
	
	public void testEnumVarTFScope() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foo;\n" +
			"	function void foobar;\n" +
			"   	enum { A, B, C } enum_var;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(getName(), content,
				new String [] {"foo", "enum_var"});
	}

	public void testStructVarTFScope() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foo;\n" +
			"	function void foobar;\n" +
			"   	struct { int A; int B; int C; } struct_var;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(getName(), content,
				new String [] {"foo", "struct_var"});
	}

	public void testMultiDimArrayDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class foo;\n" +
			"    string				my_var[][2];\n" +
			"endclass\n"
			;
		
		runTest("testMultiDimArrayDecl", content,
				new String [] {"foo", "my_var"});
	}
	
	public void testVectoredUserDefinedType() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String content =
			"class foo;\n" +
			"	typedef bit[31:0] bit32_t;\n" +
			"	function bar;\n" +
			"	int p;\n" +
			"	bit32_t [0:($bits(SZ)/$bits(bit32_t))-1] v;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest(getName(), content,
				new String [] {"foo", "v"});
	}
	
	public void testMultiDimWireArrayDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testMultiDimWireArrayDecl";
		String content =
			"module m;\n" +
			"	wire        [P1_WIDTH:0]        V1;\n" +
			"	wire        [P1_WIDTH:0][5:0]   V2;\n" +
			"	CnTxt2RAM_s [P1_WIDTH:0]        V3;\n" +
			"endmodule\n";

		runTest(testname, content,
				new String[] {"m", "V1", "V2", "V3"});
	}

	/** TODO: Await clarification
	public void testMultiDimRegArrayDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testMultiDimWireArrayDecl";
		String content =
			"module m;\n" +
			"	wire [3:0][7:0] fred;\n" +
			"endmodule\n" +
			"\n" +
			"class c;\n" +
			"	wire [3:0][7:0] barney;\n" +
			"\n" +
			"	task tf;\n" +
			"		reg [3:0][7:0] wilma;\n" +
			"	endtask\n" +
			"\n" +
			"	function void f;\n" +
			"		wire [3:0][7:0] wilma;\n" +
			"	endtask\n" +
			"endclass\n"
			;

		runTest(testname, content,
				new String[] {"m", "c", "fred", "barney", "tf"});
	}
	 */

	public void testPackedEnumArrayDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testPackedEnumArrayDecl";
		String content =
			"module m;\n" +
			"	typedef enum {A, B, C, D} my_enum_t;\n" +
			"\n" +
			"	my_enum_t [3:0]		V1[4];\n" +
			"\n" +
			"	class c;\n" +
			"		my_enum_t [3:0]		V2[4];\n" +
			"	endclass\n" +
			"\n" +
			"endmodule\n";

		runTest(testname, content,
				new String[] {"m", "c", "V1", "V2"});
	}


	public void testVirtualInterfaceParameterizedClass() throws SVParseException {
		String content =
			"class my_class\n" + 
			"	#(\n" +
			"	type vif = virtual my_inteface, // causes parse error\n" +
			"	type data = pkg_mypackage::my_datatype\n" +
			"	) extends uvm_object;\n" +
			"		// class internals\n" +
			"	endclass\n"
			;
		
		runTest("testVirtualInterfaceParameterizedClass", content,
				new String[] {"my_class"});
	}
	
	public void testVirtualInterfaceClassParam() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" + 
			"		// class internals\n" +
			"	endclass\n"
			;
		
		runTest("testVirtualInterfaceClassParam", content,
				new String[] {"my_class"});
	}
	
	public void testParamClassConstAssign() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class c;\n" +
			"	function void f();\n" +
			"		mim_request.my_ecc     = common_pkg::data_seq_item#(TXD_MIM_RQ_W)::ECC_NONE;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		runTest(getName(), content, new String[] {"c", "f"});
	}
	
	public void testStructPackedSignedUnsigned() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"typedef struct packed {\n" +
			"	int a;\n" +
			"} my_packed_struct;\n" +
			"typedef struct packed signed {\n" +
			"	int a;\n" +
			"} my_packed_signed_struct;\n" +
			"typedef struct packed unsigned {\n" +
			"	int a;\n" +
			"} my_packed_unsigned_struct;\n"
			;
		
		runTest("testStructPackedSignedUnsigned", content,
				new String[] {"my_packed_struct", "my_packed_signed_struct", "my_packed_unsigned_struct"});
	}

	public void testUnionTaggedUntagged() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"typedef union {\n" +
			"	int a;\n" +
			"	int b;\n" +
			"} my_untagged_union;\n" +
			"typedef union tagged {\n" +
			"	int a;\n" +
			"	int b;\n" +
			"} my_tagged_union;\n" +
			"typedef union tagged packed unsigned {\n" +
			"	int a;\n" +
			"	int b;\n" +
			"} my_tagged_packed_unsigned_union;\n"
			;
		
		runTest("testStructPackedSignedUnsigned", content,
				new String[] {"my_untagged_union", "my_tagged_union", "my_tagged_packed_unsigned_union"});
	}
	
	public void testIntAssignPackedStruct() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +
			"	int a;\n" +
			"	typedef struct packed {\n" +
			"		bit[15:0] a;\n" +
			"		bit[15:0] b;\n" +
    		"	} s;\n" +
    		"	initial begin\n" +
    		"		a = s'{5,10};\n" +
    		"	end\n" +
    		"endmodule\n" 
    		;
		runTest("testIntAssignPackedStruct", content,
				new String[] {"t", "a", "s"});
	}

	public void testIntAssignPackedStructFieldQualified() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"module t;\n" +											// 1
			"	int a;\n" +											
			"	typedef struct packed {\n" +
			"		bit[15:0] a;\n" +
			"		bit[15:0] b;\n" +								// 5
    		"	} s;\n" +
    		"	initial begin\n" +
    		"		a = s'{a:5, b:10, default:'x};\n" +				// 8
    		"	end\n" +
    		"endmodule\n" 
    		;
		runTest("testIntAssignPackedStructFieldQualified", content,
				new String[] {"t", "a", "s"});
	}

	public void testTimeUnits() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"class my_class extends my_base_class #(virtual my_interface);\n" +
			"\n" +
			"	function do_something;\n" +
			"		time t_s = 0.5s;\n" +
			"		time t_ms = 0.5ms;\n" +
			"		time t_us = 0.5us;\n" +
			"		time t_ns = 0.5ns;\n" +
			"		time t_ps = 0.5ps;\n" +
			"		time t_fs = 0.5fs;\n" +
			"		time t_1s = 1s;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		runTest("testTimeUnits", content,
				new String[] {"my_class", "do_something", "t_s", "t_ms", "t_us",
					"t_ns", "t_ps", "t_fs", "t_1s"});
	}
	
	public void testAssocArrayInit() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testAssocArrayInit";
		String content =
			"class foo;\n" +
			"	integer tab [string] = '{\"Peter\":20, \"Paul\":22, \"Mary\":23, default:-1 };\n" +
			"	string words [int] = '{1: \"test\", default: \"hello\"};\n" +
			"endclass\n";
		runTest(testname, content, new String[] {"foo", "tab", "words"});
	}
	
	public void testBeginBlockVirtualIfcDecl() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testBeginBlockVirtualIfcDecl";
		String content =
			"class tb_env;\n" +
			"	function void build;\n" +
			"		//------------------------------------------------\n" +
			"		// virtual interface\n" +
			"		//------------------------------------------------\n" +
			"		begin\n" +
			"			virtual pin_xactor_if #(1) int0_if;\n" +
			"		end\n" +
			"	endfunction\n" +
			"endclass\n";
		runTest(testname, content, new String[] {"tb_env", "build", "int0_if"});
	}
	
	public void testBitsConcatAssign() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testBitsConcatAssign";
		String content =
			" `define A_SIZED_TO_B(a,b) {{($bits(b)-$bits(a)){1'b0}},a}\n" +
			"\n" +
			"module top;\n" +
			" logic [4:0] fred;\n" +
			" logic [6:0] mary;\n" +
			" logic [6:0] tim;\n" +
			" always_comb\n" +
			" begin\n" +
			" tim = 5;\n" +
			" tim = `A_SIZED_TO_B(fred, mary);\n" +
			" end\n" +
			"endmodule\n"
			;
		runTest(testname, content, new String[] {"top"});
	}

	public void testMapAssign() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"typedef state_e state_q[$];\n" +
			"typedef bit[3:0] key_t;\n" +
			"typedef state_q legal_map_t[key_t];\n" +
			"typedef legal_map_t states_t[type_e];\n" +
			"\n" +
			"const states_t states = '{\n" +
			"	TYPE_E1:\n" +
			"	'{  {0, 1}: '{E1, E2, E3},\n" +
			"		{1, 2}: '{E3, E1, E2},\n" +
			"		{3, 4}: '{E3, E1, E2}\n" +
			"	},\n" +
			"	TYPE_E2:\n" +
			"	'{  0: '{E1, E2, E3},\n" +
			"		1: '{E3, E1, E2},\n" +
			"		2: '{E3, E1, E2}\n" +
			"	}\n" +
			"};\n" +
			"\n"
			;
		runTest(getName(), content, new String[] {"states"});
	}
	
	public void testScopedEnumInAssocArray() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"package my_package;\n" +
			"	typedef enum {STATE0, STATE1} state_e;\n" +
			"endpackage\n" +
			"\n" +
			"module top;\n" +
			" bit assoc_array[my_package::state_e] = '{my_package::STATE0:1'b0, my_package::STATE1:1'b1};\n" +
			"endmodule\n"
			;
		runTest(getName(), content, new String[] {"top"});
	}
	
	private void runTest(
			String			testname,
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(testname);
		SVDBFile file = SVDBTestUtils.parse(log, doc, testname, false);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}

}
