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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistModule extends SVCoreTestCaseBase {
	
	
	public void testModuleBlankItems() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m(a, b);\n" +
			"    \n" +
			"<<MARK>>	\n" +
			"	c d(a, b);\n" +
			"endmodule\n"
			;

		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"a", "b", "m", "d");
	}
	
}


