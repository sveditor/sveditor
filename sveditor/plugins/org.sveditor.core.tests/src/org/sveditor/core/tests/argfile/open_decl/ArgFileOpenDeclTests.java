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
package org.sveditor.core.tests.argfile.open_decl;

import junit.framework.TestSuite;

public class ArgFileOpenDeclTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite suite = new TestSuite("ArgFileOpenDeclTests");
		
		suite.addTest(new TestSuite(TestArgFileOpenPathDecl.class));
		
		return suite;
	}

}
