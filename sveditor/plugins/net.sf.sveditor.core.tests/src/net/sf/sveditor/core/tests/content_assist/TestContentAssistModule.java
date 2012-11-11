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


package net.sf.sveditor.core.tests.content_assist;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;

public class TestContentAssistModule extends TestCase {
	
	
	public void testModuleBlankItems() {
		String testname = "testModuleBlankItems";
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
			"module m(a, b);\n" +
			"    \n" +
			"<<MARK>>	\n" +
			"	c d(a, b);\n" +
			"endmodule\n"
			;

		ContentAssistTests.runTest(testname, doc, 
				"a", "b", "m", "d");
	}
	
}


