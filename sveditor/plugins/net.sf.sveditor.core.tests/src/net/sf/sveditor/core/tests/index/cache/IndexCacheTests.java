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


package net.sf.sveditor.core.tests.index.cache;

import junit.framework.Test;
import junit.framework.TestSuite;

public class IndexCacheTests extends TestSuite {

	public static Test suite() {
		TestSuite suite = new TestSuite("IndexTests");
//		suite.addTest(new TestSuite(TestIndexCache.class));
		suite.addTest(new TestSuite(TestSegmentedCache.class));
		
		return suite;
	}

}
