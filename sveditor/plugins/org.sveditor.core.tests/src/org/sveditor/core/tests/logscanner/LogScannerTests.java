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
package org.sveditor.core.tests.logscanner;

import junit.framework.TestSuite;

public class LogScannerTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite ret = new TestSuite();
		
		ret.addTest(new TestSuite(TestQuestaLogScanner.class));
		ret.addTest(new TestSuite(TestVerilatorLogScanner.class));
		ret.addTest(new TestSuite(TestMakefileLogScanner.class));
		ret.addTest(new TestSuite(TestNCSimLogScanner.class));
		
		return ret;
	}

}
