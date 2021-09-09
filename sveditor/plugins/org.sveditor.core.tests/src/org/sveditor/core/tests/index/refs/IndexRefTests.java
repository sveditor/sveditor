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
package org.sveditor.core.tests.index.refs;

import junit.framework.Test;
import junit.framework.TestSuite;

public class IndexRefTests extends TestSuite {

	public static Test suite() {
		TestSuite suite = new TestSuite("IndexRefTests");
		
		suite.addTest(new TestSuite(TestInstanceTreeFactory.class));
		suite.addTest(new TestSuite(TestClassRefs.class));
		
		return suite;
	}
}
