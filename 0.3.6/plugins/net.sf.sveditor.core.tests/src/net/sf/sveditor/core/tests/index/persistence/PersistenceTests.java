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


package net.sf.sveditor.core.tests.index.persistence;

import junit.framework.Test;
import junit.framework.TestSuite;

public class PersistenceTests {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("PersistenceTests");
		suite.addTest(new TestSuite(TestFilesystemLibPersistence.class));
		suite.addTest(new TestSuite(TestWorkspaceLibPersistence.class));
		suite.addTest(new TestSuite(ArgFilePersistence.class));
		suite.addTest(new TestSuite(SrcCollectionPersistence.class));
		
		return suite;
	}

}
