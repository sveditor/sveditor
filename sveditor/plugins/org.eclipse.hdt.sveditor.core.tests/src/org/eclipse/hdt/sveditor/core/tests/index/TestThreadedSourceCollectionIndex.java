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
package net.sf.sveditor.core.tests.index;

import java.io.File;

import junit.framework.TestCase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestThreadedSourceCollectionIndex extends TestCase {
	private File			fTmpDir;

	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}
	
}
