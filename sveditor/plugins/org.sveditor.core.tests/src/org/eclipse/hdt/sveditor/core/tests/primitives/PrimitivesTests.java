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
package org.eclipse.hdt.sveditor.core.tests.primitives;

import junit.framework.TestSuite;

public class PrimitivesTests extends TestSuite {
	
	
	public static TestSuite suite() {
		TestSuite suite = new TestSuite();
		suite.addTest(new TestSuite(TestStringTextScanner.class));
		
		return suite;
	}

}
