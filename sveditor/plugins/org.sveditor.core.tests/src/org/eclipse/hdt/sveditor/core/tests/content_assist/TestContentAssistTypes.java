/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import junit.framework.TestCase;

public class TestContentAssistTypes extends SVCoreTestCaseBase {
	
	public void testTypeAssistPackageScope() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testTypeAssistPackageScope";
		String doc =
				"package pkg;\n" +
				"	typedef int unsigned my_int32_type;\n" +
				"	typedef longint unsigned my_int64_type;\n" +
				"endpackage\n" +
				"\n" +
				"class c;\n" +
				"	pkg::my_<<MARK>>\n" +
				"endclass\n"
				;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"my_int32_type", "my_int64_type");
	}

	public void testEnumAssistPackageScope() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testEnumAssistPackageScope";
		String doc =
				"package pkg;\n" +
				"	typedef enum {\n" +
				"		MY_ENUM_A,\n" +
				"		MY_ENUM_B\n" +
				"	} my_enum_t;\n" +
				"endpackage\n" +
				"\n" +
				"class c;\n" +
				"	pkg::my_<<MARK>>\n" +
				"endclass\n"
				;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"my_enum_t", "MY_ENUM_A", "MY_ENUM_B");
	}

	public void testTypeAssistClassScope() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testTypeAssistClassScope";
		String doc =
				"class src_c;\n" +
				"	typedef int unsigned my_int32_type;\n" +
				"	typedef longint unsigned my_int64_type;\n" +
				"endclass\n" +
				"\n" +
				"class c;\n" +
				"	src_c::my_<<MARK>>\n" +
				"endclass\n"
				;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"my_int32_type", "my_int64_type");
	}

	public void testEnumAssistClassScope() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testEnumAssistClassScope";
		String doc =
				"class src_c;\n" +
				"	typedef enum {\n" +
				"		MY_ENUM_A,\n" +
				"		MY_ENUM_B\n" +
				"	} my_enum_t;\n" +
				"endclass\n" +
				"\n" +
				"class c;\n" +
				"	src_c::my_<<MARK>>\n" +
				"endclass\n"
				;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc,
				"my_enum_t", "MY_ENUM_A", "MY_ENUM_B");
	}
	
	public void testClassParam() {
		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testEnumAssistClassScope";
		String doc =
				"class src_c #(type my_type=int);\n" +
				"\n" +
				"	function src_c();\n" +
				"		my_<<MARK>>\n" +
				"	endfunction\n" +
				"endclass\n"
				;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"my_type");
	}

}
