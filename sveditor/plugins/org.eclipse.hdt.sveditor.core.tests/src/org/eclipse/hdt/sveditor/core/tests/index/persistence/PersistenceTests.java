/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package net.sf.sveditor.core.tests.index.persistence;

import junit.framework.Test;
import junit.framework.TestSuite;

public class PersistenceTests {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("PersistenceTests");
//		suite.addTest(new TestSuite(TestFilesystemLibPersistence.class));
//		suite.addTest(new TestSuite(TestWorkspaceLibPersistence.class));
		suite.addTest(new TestSuite(ArgFilePersistence.class));
		suite.addTest(new TestSuite(TestPersistenceUnit.class));
		suite.addTest(new TestSuite(TestSVDBFileSystem.class));
		suite.addTest(new TestSuite(TestSVDBFileIndexCacheMgr.class));
		
		return suite;
	}
	

}
