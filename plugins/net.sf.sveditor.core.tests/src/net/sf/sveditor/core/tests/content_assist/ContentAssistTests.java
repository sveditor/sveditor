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


package net.sf.sveditor.core.tests.content_assist;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class ContentAssistTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("ContentAssistTests");
		suite.addTest(new TestSuite(ContentAssistBasics.class));
		
		return suite;
	}

}
