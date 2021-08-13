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


package org.eclipse.hdt.sveditor.core.tests.parser;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.SVDBUtil;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.parser.SVParser;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;

import junit.framework.TestCase;

public class TestParseFunction extends TestCase {
	

	private SVDBTask parse_tf(String content, String name) throws SVParseException {
		return parse_tf(null, content, name);
	}
	
	private SVDBTask parse_tf(SVParserConfig config, String content, String name) throws SVParseException {
		SVDBScopeItem scope = new SVDBScopeItem();
		SVParser parser = new SVParser();
		parser.init(new StringInputStream(content), name);
		
		if (config != null) {
			parser.setConfig(config);
		}
		
		parser.parsers().taskFuncParser().parse(scope, -1, 0);

		return (SVDBTask)scope.getChildren().iterator().next();
	}

	private SVDBClassDecl parse_class(String content, String name) throws SVParseException {
		SVDBScopeItem scope = new SVDBScopeItem();
		SVParser parser = new SVParser();
		parser.init(new StringInputStream(content), name);
		
		parser.parsers().classParser().parse(scope, 0);

		return (SVDBClassDecl)scope.getChildren().iterator().next();
	}

	public void testBasicFunction() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		parse_tf(content, "testBasicFunction");
	}

	public void testReturnOnlyFunction() throws SVParseException {
		String content =
			"class foobar;\n" +
			"local virtual function string foobar();\n" +
			"    return \"foobar\";\n" +
			"endfunction\n" +
			"endclass\n"
			;
		parse_class(content, "testReturnOnlyFunction");
	}
	
	public void testKRParameters() throws SVParseException {
		String testname = "testKRParameters";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"function automatic integer f;\n" +
			"	input integer in; // error.\n" +
			"begin\n" +
			"end\n" +
			"endfunction\n"
			;
		parse_tf(content, testname);
	}

	public void testKRParameters2() throws SVParseException {
		String testname = "testKRParameters2";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"	task send_rx_packet;\n" +
			"		input  [(8*8)-1:0] preamble_data;\n" +   
			"		input   [3:0] preamble_len;\n" + 
			"		input   [7:0] sfd_data;\n" +
			"		input  [31:0] start_addr;\n" +
			"		input  [31:0] len;\n" +
			"		input         plus_drible_nibble;\n" +
			"		integer       rx_cnt;\n" +
			"		reg    [31:0] rx_mem_addr_in;\n" +       
			"		reg     [7:0] rx_mem_data_out;\n" +
			"	begin\n" + 
		    "		@(posedge mrx_clk_o);\n" +
			"	end\n" +
		    "	endtask\n"
		    ;
		parse_tf(content, testname);
	}

	public void testTaskWithParam() throws SVParseException {
		String testname = "testTaskWithParam";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			"	task send_rx_packet;\n" +
			"		parameter PARAM1 = 1;\n" +
			"		begin\n" +
			"			parameter PARAM2 = 1;\n" +   
			"		end\n" +
		    "	endtask\n"
		    ;
		parse_tf(content, testname);
	}

	public void testTaskWithUnion() throws SVParseException {
		String testname = "testTaskWithUnion";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
			" task test_with_union;\n" +
			"   union packed {\n" +
			"       logic [31:0] vector;\n" +
			"       struct packed {\n" +
			"          logic[31:16] top;\n" +
			"          logic[15:0] bottom;\n" +
			"       } fields;\n" +
			"   } union_xyz;\n" +
			" endtask;\n"
		    ;
		parse_tf(content, testname);
		
	}

	// Tests that local variables are correctly recognized and that 
	// cast expressions are skipped appropriately
	public void testLocalVarsWithCast() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    int a = integer'(5);\n" +
			"    int b = longint'(6);\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBTask func = parse_tf(content, "testLocalVarsWithCast");

		assertEquals(3, SVDBUtil.getChildrenSize(func)); 
		SVDBVarDeclItem a=null, b=null;
		for (ISVDBItemBase it_t : func.getChildren()) {
			if (it_t.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)it_t;
				for (ISVDBChildItem vi : v.getChildren()) {
					if (SVDBItem.getName(vi).equals("a")) {
						a = (SVDBVarDeclItem)vi;
					} else if (SVDBItem.getName(vi).equals("b")) {
						b = (SVDBVarDeclItem)vi;
					}
				}
			}
		}
		assertNotNull(a);
		assertNotNull(b);
	}

	// Tests that local variables are correctly recognized and that 
	// cast expressions are skipped appropriately
	public void testLocalTimeVar() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    time t = 10ns;\n" +
			"    t = 20ns;\n" +
			"endfunction\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBTask func = parse_tf(content, "testLocalTimeVar");

		assertEquals(2, SVDBUtil.getChildrenSize(func));
		assertTrue(SVDBUtil.getFirstChildItem(func).getType() == SVDBItemType.VarDeclStmt);
		SVDBVarDeclStmt stmt = (SVDBVarDeclStmt)SVDBUtil.getFirstChildItem(func);
		SVDBVarDeclItem vi = (SVDBVarDeclItem)stmt.getChildren().iterator().next();
		assertEquals("t", vi.getName());
	}

	// Tests that local variables are correctly recognized and that 
	// cast expressions are skipped appropriately
	public void testLocalTypedef() throws SVParseException {
		String content =
			"function void foobar();\n" +
			"    typedef foo #(BAR) foo_t;\n" +
			"    foo_t              a;\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
//		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		
		SVDBTask func = parse_tf(content, "testLocalTypedef");
		
		SVDBVarDeclItem a=null;
		for (ISVDBItemBase it : func.getChildren()) {
			if (it.getType() == SVDBItemType.VarDeclStmt) {
				for (ISVDBChildItem vi : ((SVDBVarDeclStmt)it).getChildren()) {
					if (SVDBItem.getName(vi).equals("a")) {
						a = (SVDBVarDeclItem)vi;
					}
				}
			}
		}

		assertEquals(3, SVDBUtil.getChildrenSize(func));
		assertEquals("foo_t", SVDBItem.getName(SVDBUtil.getFirstChildItem(func)));
		assertNotNull(a);
	}

	public void testStaticFunction() throws SVParseException {
		String content =
			"function static void foobar();\n" +
			"    int a;\n" +
			// "    a = 5;\n" +
			"endfunction\n";
		
//		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parse_tf(content, "testStaticFunction");
	}
	
	public void testIfElseBody() throws SVParseException {
		String content =
			"function new();\n" +
			"    string ini_file;\n" +
			"\n" +
		    "    if ($value$plusargs(\"INFACT_AXI_FULL_PROTOCOL_INI=%s\", ini_file)) begin\n" +
			"        ovm_report_info(\"INFACT_AXI_FULL_PROTOCOL\",\n" + 
			"            {\"Loading parameters from .ini file \", ini_file});\n" +
			"        load_ini(ini_file);\n" +
			"    end else begin\n" +
			"        ovm_report_info(\"INFACT_AXI_FULL_PROTOCOL\",\n" + 
			"            {\"No .ini file specified\"});\n" +
			"    end\n" +
			"endfunction\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		
		parse_tf(content, "testIfElseBody");
	}

	public void testIfInside() throws SVParseException {
		String content =
			"task atask;\n" +
			"int a_thing ;\n" +
			"if( !(a_thing inside things)) begin\n" +
			"	$display(\"Arggg!\n\") ;\n" +
			"end\n" +
			"endtask\n"				
			;
		SVParserConfig config = new SVParserConfig();
		
		config.setAllowInsideQWithoutBraces(true);
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		parse_tf(config, content, "testIfInside");
	}

	public void testAutomaticFunction() throws SVParseException {
		String content =
			"function automatic void foobar();\n" +
			"    a = 5;\n" +
			"endfunction\n";
		
//		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		
		parse_tf(content, "testAutomaticFunction");
	}

	public void testParamListFunction() throws SVParseException {
		String content =
			"function automatic void foobar(\n" +			// 1
			"        input int foobar,\n" +					// 2
			"        ref object bar,\n" +					// 3
			"        int foo);\n" +							// 4
			"    a_type foo, bar;\n" +						// 5
			"    b_type foo_q[$];\n" +						// 6
			"    b_cls #(foobar, bar) elem;\n" +
			"    int i, j, k;\n" +
			"    for (int i=0; i<5; i++) begin\n" +
			"        a = 5;\n" +
			"    end\n" +
			"endfunction\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBTask func = parse_tf(content, "testParamListFunction");
		
		ISVDBChildItem c = func.getParams().get(1).getChildren().iterator().next();
				
		assertEquals("bar", SVDBItem.getName(c));
		assertEquals(SVDBParamPortDecl.Direction_Ref,
				func.getParams().get(1).getDir());
	}

	public void testParamListFunctionWithPkg() throws SVParseException {
		String content =
			"function automatic void foobar(\n" +	
			"        input int foobar,\n" +			
			"        ref object bar,\n" +			
			"        int foo);\n" +					
			"    a_type foo, bar;\n" +				
			"    b_type foo_q[$];\n" +				
			"    int i, j, k;\n" +
			"    uvm_pkg::uvm_resource_db #(my_pkg::my_iface_container #(virtual my_iface)) " +
			"        ::set(\"my_ifaces\", $sformatf(\"my_iface_%01d\",0), ifc) ;" +
			"    for (int i=0; i<5; i++) begin\n" +
			"        a = 5;\n" +
			"    end\n" +
			"endfunction\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBTask func = parse_tf(content, "testParamListFunction");
		
		ISVDBChildItem c = func.getParams().get(1).getChildren().iterator().next();
				
		assertEquals("bar", SVDBItem.getName(c));
		assertEquals(SVDBParamPortDecl.Direction_Ref,
				func.getParams().get(1).getDir());
	}

}
