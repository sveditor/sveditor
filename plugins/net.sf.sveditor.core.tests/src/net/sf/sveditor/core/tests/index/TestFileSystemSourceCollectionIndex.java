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


package net.sf.sveditor.core.tests.index;

import java.io.File;

import net.sf.sveditor.core.tests.utils.TestUtils;

import junit.framework.TestCase;

public class TestFileSystemSourceCollectionIndex extends TestCase {
	private File			fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}
	
//	public void testDefaultSourceCollection

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
		}
	}
	
	

}
