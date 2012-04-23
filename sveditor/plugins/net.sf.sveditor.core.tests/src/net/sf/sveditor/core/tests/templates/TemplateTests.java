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


package net.sf.sveditor.core.tests.templates;

import junit.framework.TestSuite;

public class TemplateTests extends TestSuite {

	public static TestSuite suite() {
		TestSuite s = new TestSuite();
		s.addTest(new TestSuite(TestMethodologyTemplates.class));
		s.addTest(new TestSuite(TestExternalTemplates.class));
		return s;
	}
}
