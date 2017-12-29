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


package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestModuleContentAssist extends SVCoreTestCaseBase {

	public void testModulePortAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1(input AAAA, output BBBB);\n" +
				"endmodule\n" +
				"\n" +
				"module m2;\n" +
				"\n" +
				"	m1 m(.A<<MARK>>\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "AAAA");
	}

	public void testModulePortAssistNoPrefix() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1(input AAAA, output BBBB);\n" +
				"endmodule\n" +
				"\n" +
				"module m2;\n" +
				"\n" +
				"	m1 m(.<<MARK>>\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "AAAA", "BBBB");
	}

	public void testInitialBlockVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1(input AAAA, output BBBB);\n" +
				"	initial begin\n" +
				"		int ABAA, AABB, c;\n" +
				"		c = A<<MARK>>\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "AAAA", "ABAA", "AABB");
	}
	
	public void testNestedBlockVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"module m1;\n" +
				"	initial begin\n" +
				"		int AAAA, AABB, c;\n" +
				"		begin\n" +
				"			int ABAB;\n" +
				"			c = A<<MARK>>\n" +
				"		end\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, 
				"AAAA", "AABB", "ABAB");
	}
	
	public void testNestedIfVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1;\n" +							// 1
				"	initial begin\n" +						// 2
				"		int AAAA, AABB, c;\n" +				// 3
				"		if (AAAA == 2) begin\n" +			// 4
				"			int ABAB;\n" +					// 5
				"			if (AABB == 3) begin\n" +		// 6
				"				int AABA;\n" +
				"				c = A<<MARK>>\n" +
				"			end\n" +
				"		end\n" +
				"		end\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, 
				"AABA", "AAAA", "AABB", "ABAB");
	}	

	public void testNestedWhileVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1;\n" +							// 1
				"	initial begin\n" +						// 2
				"		int AAAA, AABB, c;\n" +				// 3
				"		while (AAAA == 2) begin\n" +			// 4
				"			int ABAB;\n" +					// 5
				"			while (AABB == 3) begin\n" +		// 6
				"				int AABA;\n" +
				"				c = A<<MARK>>\n" +
				"			end\n" +
				"		end\n" +
				"		end\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, 
				"AABA", "AAAA", "AABB", "ABAB");
	}

	public void testNestedDoWhileVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1;\n" +							// 1
				"	initial begin\n" +						// 2
				"		int AAAA, AABB, c;\n" +				// 3
				"			do begin\n" +			// 4
				"				int ABAB;\n" +					// 5
				"				do begin\n" +		// 6
				"					int AABA;\n" +
				"					c = A<<MARK>>\n" +
				"				end while (AABB == 3);\n" +
				"			end while (AAAA == 2);\n" +
				"		end\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, 
				"AAAA", "AABB", "ABAB", "AABA");
	}

	public void testNestedRepeatVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1;\n" +							// 1
				"	initial begin\n" +						// 2
				"		int AAAA, AABB, c;\n" +				// 3
				"			repeat (10) begin\n" +			// 4
				"				int ABAB;\n" +					// 5
				"				repeat (20) begin\n" +		// 6
				"					int AABA;\n" +
				"					c = A<<MARK>>\n" +
				"				end while (AABB == 3);\n" +
				"			end while (AAAA == 2);\n" +
				"		end\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, 
				"AAAA", "AABB", "ABAB", "AABA");
	}

	public void testNestedForeverVariableAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module m1;\n" +							// 1
				"	initial begin\n" +						// 2
				"		int AAAA, AABB, c;\n" +				// 3
				"			forever begin\n" +			// 4
				"				int ABAB;\n" +					// 5
				"				forever begin\n" +		// 6
				"					int AABA;\n" +
				"					c = A<<MARK>>\n" +
				"				end while (AABB == 3);\n" +
				"			end while (AAAA == 2);\n" +
				"		end\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, 
				"AAAA", "AABB", "ABAB", "AABA");
	}
	
	public void testInitialBlockVarFieldAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"	class foo;\n" +
				"		int AAAA;\n" +
				"		int AABB;\n" +
				"	endclass\n" +
				"\n" +
				"module m1(input AAAA, output BBBB);\n" +
				"	initial begin\n" +
				"		foo c;\n" +
				"		c.A<<MARK>>\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "AAAA", "AABB");
	}

	public void testModuleHierarchyAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module sub;\n" +
				"		int AAAA;\n" +
				"		int AABB;\n" +
				"endmodule\n" +
				"\n" +
				"module m1(input AAAA, output BBBB);\n" +
				"	sub		u1;\n" +
				"\n" +
				"	initial begin\n" +
				"		u<<MARK>>\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "u1");
	}

	public void testModuleHierarchyAssist_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module sub;\n" +
				"		int AAAA;\n" +
				"		int AABB;\n" +
				"endmodule\n" +
				"\n" +
				"module m1(input AAAA, output BBBB);\n" +
				"	sub		u1;\n" +
				"\n" +
				"	initial begin\n" +
				"		u1.AA<<MARK>>\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "AAAA", "AABB");
	}

	public void testModuleHierarchyAssist_3() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc = 
				"module sub;\n" +
				"		int AAAA;\n" +
				"		int AABB;\n" +
				"endmodule\n" +
				"\n" +
				"module sub_1;\n" +
				"		sub s1();\n" +
				"endmodule\n" +
				"\n" +
				"module m1(input AAAA, output BBBB);\n" +
				"	sub_1	u1;\n" +
				"\n" +
				"	initial begin\n" +
				"		u1.s1.AA<<MARK>>\n" +
				"	end\n" +
				"endmodule\n"
				;
		ContentAssistTests.runTest(this, doc, "AAAA", "AABB");
	}
}
