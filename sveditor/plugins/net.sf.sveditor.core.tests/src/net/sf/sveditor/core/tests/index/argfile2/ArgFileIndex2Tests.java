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
package net.sf.sveditor.core.tests.index.argfile2;

import junit.framework.TestSuite;

public class ArgFileIndex2Tests extends TestSuite {
	
	public ArgFileIndex2Tests() {
		addTest(new TestSuite(TestArgFileChange.class));
		addTest(new TestSuite(TestGetFilePath.class));
		addTest(new TestSuite(TestSVDBIndexUtil.class));
	}
	
	public static TestSuite suite() {
		return new ArgFileIndex2Tests();
	}

}
