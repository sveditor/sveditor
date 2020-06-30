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


package org.eclipse.hdt.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestParserErrorRecovery extends TestCase {
	
	public void testModuleScopeError() {
		LogHandle log = LogFactory.getLogHandle("testModuleScopeError");
		String content = 
			"module foo;\n" +
			"	wire a;\n" +
			"	reg b[;\n" + // Error
			"	reg c;\n" +
			"endmodule\n" +
			"\n" +
			"module bar;\n" +
			"endmodule\n"
			;
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = SVDBTestUtils.parse(log, content, 
				"testModuleScopeError", markers);
		
		assertEquals(1, markers.size());
		SVDBTestUtils.assertFileHasElements(file, new String[] {"foo", "a", "c", "bar"});
		
		LogFactory.removeLogHandle(log);
	}

	public void testClassScopeError() {
		LogHandle log = LogFactory.getLogHandle("testClassScopeError");
		String content = 
			"class foo;\n" +
			"	bit a;\n" +
			"	bit b[;\n" + // Error
			"	bit c;\n" +
			"endclass\n" +
			"\n" +
			"class bar;\n" +
			"endclass\n"
			;
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = SVDBTestUtils.parse(log, content, 
				"testClassScopeError", markers);
		
		assertEquals(1, markers.size());
		SVDBTestUtils.assertFileHasElements(file, new String[] {"foo", "a", "bar"});
		
		LogFactory.removeLogHandle(log);
	}

	public void EXP_FAIL_testTFScopeError() {
		LogHandle log = LogFactory.getLogHandle("testTFScopeError");
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"class foo;\n" +
			"	bit a;\n" +
			"	function void foo_func();\n" +
			"		if (bar\n" + // Error
			"		end\n" +
			"	endfunction\n" +
			"	bit c;\n" +
			"endclass\n" +
			"\n" +
			"class bar;\n" +
			"endclass\n"
			;
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = SVDBTestUtils.parse(log, content, 
				"testTFScopeError", markers);
		
		assertEquals(2, markers.size());
		SVDBTestUtils.assertFileHasElements(file, new String[] {"foo", "a", "c", "bar"});
		
		LogFactory.removeLogHandle(log);
	}

}
