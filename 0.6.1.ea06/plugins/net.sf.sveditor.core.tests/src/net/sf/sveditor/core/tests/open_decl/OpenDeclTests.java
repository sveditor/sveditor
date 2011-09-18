/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.open_decl;

import junit.framework.TestSuite;

public class OpenDeclTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("OpenDeclTests");
		s.addTest(new TestSuite(TestOpenFile.class));
		s.addTest(new TestSuite(TestOpenClass.class));
		s.addTest(new TestSuite(TestOpenModIfc.class));
		
		return s;
	}
	

}
