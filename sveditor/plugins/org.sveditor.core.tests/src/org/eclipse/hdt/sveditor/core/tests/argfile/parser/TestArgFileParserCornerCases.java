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
package org.eclipse.hdt.sveditor.core.tests.argfile.parser;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import org.eclipse.hdt.sveditor.core.db.argfile.SVDBArgFileStmt;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;

public class TestArgFileParserCornerCases extends TestCase {

	public void testMissingArgFileIncPath() throws SVParseException {
		String testname = "testArgFileInc";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"-f /tools/argfiles/argfile1.f\n" +
				"-file /tools/argfiles/argfile2.f\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, 
				new SVDBMarker[] {
				},
				new SVDBArgFileStmt[] {
					new SVDBArgFileIncFileStmt("/tools/argfiles/argfile1.f"),
					new SVDBArgFileIncFileStmt("/tools/argfiles/argfile2.f")
				});		
	}
}
