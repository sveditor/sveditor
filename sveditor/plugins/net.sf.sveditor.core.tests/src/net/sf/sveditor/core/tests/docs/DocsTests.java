
/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.tests.docs ;

import junit.framework.TestSuite ;

public class DocsTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("DocsTests");
		s.addTest(new TestSuite(TestCleaner.class));
		s.addTest(new TestSuite(TestParser.class));
		s.addTest(new TestSuite(TestModelFactory.class));
		s.addTest(new TestSuite(TestFindDocComments.class));
		return s;
	}

}
