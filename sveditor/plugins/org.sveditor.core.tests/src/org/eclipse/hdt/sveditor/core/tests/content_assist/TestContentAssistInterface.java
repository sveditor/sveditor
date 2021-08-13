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


package org.eclipse.hdt.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistInterface extends SVCoreTestCaseBase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistInterfaceBasics() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"interface foo_if;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endinterface\n" +
			"\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	virtual foo_if			m_foo_if;\n" +
			"	m_foo_if.<<MARK>>\n" +
			"endtask\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB", "BBCC");
	}

	public void testInterfaceTaskVarAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	task f;\n" +
				"		AA<<MARK>>\n" +
				"	endtask\n" +
				"endinterface\n"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	public void testInterfaceModuleFieldAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top;\n" +
				"	i1		ifc_if();\n" +
				"\n" +
				"	submodule s1(" +
				"		.p1(if<<MARK>>\n" +
				"	);\n" +
				"endmodule"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"ifc_if");
	}
	
	public void testInterfaceModulePortAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1(input clk, input rst);\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top;\n" +
				"	i1		ifc_if();\n" +
				"\n" +
				"	submodule s1(" +
				"		.p1(ifc_if.c<<MARK>>\n" +
				"	);\n" +
				"endmodule"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"clk");
	}	
	
	public void testInterfaceModportModuleField() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	modport foo(input AAAA, AABB, BBBB);\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top;\n" +
				"	i1		ifc_if();\n" +
				"\n" +
				"	submodule s1(" +
				"		.p1(ifc_if.f<<MARK>>\n" +
				"	);\n" +
				"endmodule"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"foo");
	}
	
	public void testInterfaceModportModulePort() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	modport foo(input AAAA, AABB, BBBB);\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top(" +
				"	i1.foo		foo_p" +
				"	);\n" +
				"\n" +
				"	initial begin\n" +
				"		foo_p.AA<<MARK>>\n" +
				"	end\n" +
				"endmodule"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}
	
	public void testInterfaceModportModulePort_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	modport foo(input AAAA, AABB, BBBB);\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top(" +
				"	i1.foo		p_foo" +
				"	);\n" +
				"\n" +
				"	initial begin\n" +
				"		p_<<MARK>>\n" +
				"	end\n" +
				"endmodule"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"p_foo");
	}

	public void testInterfaceInstParamAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"interface i1 #(parameter int AAAA=1, parameter int AABB=2, parameter int BBBB=3) ();\n" +
				"\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top();\n" +
				"\n" +
				"	i1 #(\n" +
				"		.AA<<MARK>>\n" +
				"	) i1_inst();\n" +
				"endmodule"
				;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}
}


