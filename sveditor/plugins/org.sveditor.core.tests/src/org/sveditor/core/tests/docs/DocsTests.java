
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
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package org.sveditor.core.tests.docs ;

import junit.framework.TestSuite ;

public class DocsTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("DocsTests");
		s.addTest(new TestSuite(TestCleaner.class));
		s.addTest(new TestSuite(TestParser.class));
//		s.addTest(new TestSuite(TestModelFactory.class));
		s.addTest(new TestSuite(TestFindDocComments.class));
		return s;
	}

}
