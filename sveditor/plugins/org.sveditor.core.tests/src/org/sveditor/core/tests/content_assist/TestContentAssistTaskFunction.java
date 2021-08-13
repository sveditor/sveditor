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


package org.sveditor.core.tests.content_assist;

import org.sveditor.core.SVCorePlugin;

import org.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistTaskFunction extends SVCoreTestCaseBase {
	
	
	/**
	 * Test we can find and use task/function parameters
	 */
	public void testClassTFParam() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task(foobar param);\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task(foobar param);\n" +
			"	param.AA<<MARK>>\n" +
			"endtask\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	/**
	 * Test we can find and use task/function local vars
	 */
	public void testClassTFLocal() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	foobar param;\n" +
			"	param.AA<<MARK>>\n" +
			"endtask\n"
			;
				
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

	/**
	 * Test we can find and use task/function local vars
	 */
	public void testClassTFSameClassLocal() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"\n" +
			"	static function int f();\n" +
			"		foobar inst;\n" +
			"\n" +
			"		return inst.A<<MARK>>\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
	}

}
