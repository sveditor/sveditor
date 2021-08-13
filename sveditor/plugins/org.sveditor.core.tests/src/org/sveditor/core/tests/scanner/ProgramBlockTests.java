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


package org.sveditor.core.tests.scanner;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.StringInputStream;
import org.sveditor.core.db.ISVDBFileFactory;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;

import junit.framework.TestCase;
import org.sveditor.core.tests.SVDBTestUtils;

public class ProgramBlockTests extends TestCase {
	

	protected void setUp() throws Exception {
		super.setUp();
	}
	
	public void testBasicProgramBlock() {
		StringInputStream in = new StringInputStream(
				"\n\n\n" +
				"class foo;\n" +
				"endclass\n" + 
				"program foobar;\n" +
				"endprogram\n" +
				"class foo_c;\n" +
				"endclass\n" +
				"\n\n\n\n");
		ISVDBFileFactory f = SVCorePlugin.createFileFactory();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = f.parse(in, "test", markers);
		
		SVDBTestUtils.assertFileHasElements(file, "foo", "foobar", "foo_c");
	}

	protected void tearDown() throws Exception {
		super.tearDown();
	}

}
