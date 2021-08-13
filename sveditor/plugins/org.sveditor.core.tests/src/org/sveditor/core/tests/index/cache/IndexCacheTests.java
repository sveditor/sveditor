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


package org.sveditor.core.tests.index.cache;

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
