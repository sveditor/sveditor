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
package org.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.StringInputStream;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.parser.SVLanguageLevel;
import org.sveditor.core.parser.SVParseException;
import org.sveditor.core.parser.SVParserConfig;

import junit.framework.TestCase;
import org.sveditor.core.tests.SVDBTestUtils;

public class TestParseClassDecl extends TestCase {
	
	public void testParseGlobalInterfaceClassDeclaration() throws SVParseException {
		String content = 
				"interface class foobar;\n" +
				"endclass\n"
				;
		
		runTest(content, new String[] {"foobar"});
	}
	
	public void testParsePackageInterfaceClassDeclaration() throws SVParseException {
		String content = 
				"package my_pkg;\n" +
				"	interface class foobar;\n" +
				"	endclass\n" +
				"endpackage\n"
				;
		
		runTest(content, new String[] {"my_pkg", "foobar"});
	}

	public void testParseModuleInterfaceClassDeclaration() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"module top;\n" +
				"	interface class foobar;\n" +
				"	endclass\n" +
				"endmodule\n"
				;
		
		runTest(content, new String[] {"top", "foobar"});
	}

	public void testParseClassParamExtNoHash() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"package my_pkg;\n" +
				"	class base;\n" +
				"	endclass\n" +
				"\n" +
				"	class ext extends base();\n" +
				"	endclass\n" +
				"endpackage\n"
				;
		
		runTest(content, new String[] {"my_pkg", "base", "ext"});
	}
	
	private void runTest(
			String			doc,
			String			exp_items[]) {
		runTest(null, getName(), doc, exp_items);
	}

	private void runTest(
			SVParserConfig	config,
			String			testname,
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> result = SVDBTestUtils.parse(
				log, SVLanguageLevel.SystemVerilog, config, 
				new StringInputStream(doc), testname, markers);
		
		SVDBFile file = result.second();
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}
}
