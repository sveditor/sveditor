/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.core.tests.preproc;

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
