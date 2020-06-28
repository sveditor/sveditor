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


package net.sf.sveditor.core.tests.content_assist;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestContentAssistBuiltins extends SVCoreTestCaseBase {
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();

		fIndexRgy.close();
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testCovergroupOption() {
		String doc =
			"class my_class1;\n" +							// 1
			"\n" +											// 2
			"    covergroup foo;\n" +						// 3
			"        option.per_<<MARK>>\n" +				// 4
			"    endgroup\n" +
			"endclass\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		ContentAssistTests.runTest(this, doc, "per_instance");
	}

	public void testCovergroupTypeOptionMergeInstances() {
		String doc =
			"class my_class1;\n" +							// 1
			"\n" +
			"    covergroup foo;\n" +
			"        type_option.mer<<MARK>>\n" +
			"    endgroup\n" +
			"endclass\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		ContentAssistTests.runTest(this, doc, "merge_instances");
	}
}
