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


package net.sf.sveditor.core.tests.scanner;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.tests.SVDBTestUtils;

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
		ISVDBFileFactory f = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = f.parse(in, "test", markers);
		
		SVDBTestUtils.assertFileHasElements(file, "foo", "foobar", "foo_c");
	}

	protected void tearDown() throws Exception {
		super.tearDown();
	}

}
