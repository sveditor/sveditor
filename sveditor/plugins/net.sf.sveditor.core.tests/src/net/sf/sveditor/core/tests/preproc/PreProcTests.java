/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.preproc;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class PreProcTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("PreProcTests");
		suite.addTest(new TestSuite(TestPreProc.class));
		suite.addTest(new TestSuite(TestPreProc2.class));
		suite.addTest(new TestSuite(TestPreProcLexer2.class));
		suite.addTest(new TestSuite(TestPreProcListener.class));
		suite.addTest(new TestSuite(TestPreProcLineNumbers.class));
		return suite;
	}

}
