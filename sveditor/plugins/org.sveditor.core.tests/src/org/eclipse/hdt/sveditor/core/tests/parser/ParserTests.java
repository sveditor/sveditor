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


package org.eclipse.hdt.sveditor.core.tests.parser;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVLanguageLevel;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;
import junit.framework.TestSuite;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;

public class ParserTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ParserTests");
		s.addTest(new TestSuite(TestLexer.class));
		s.addTest(new TestSuite(TestParseBehavioralStmts.class));
		s.addTest(new TestSuite(TestParseClassBodyItems.class));
		s.addTest(new TestSuite(TestParseClassDecl.class));
		s.addTest(new TestSuite(TestParserClockingBlock.class));
		s.addTest(new TestSuite(TestParseConfigurations.class));
		s.addTest(new TestSuite(TestParseConstraints.class));
		
		s.addTest(new TestSuite(TestParseDataTypes.class));
		s.addTest(new TestSuite(TestParseDpiTF.class));
		s.addTest(new TestSuite(TestParseExpr.class));
		s.addTest(new TestSuite(TestParseErrors.class));
		s.addTest(new TestSuite(TestParseFunction.class));
		s.addTest(new TestSuite(TestParseInterfaceBodyItems.class));
		s.addTest(new TestSuite(TestParseInterfaceClassDecl.class));
		// LineNumbers
		s.addTest(new TestSuite(TestParseLineNumbers.class));
		s.addTest(new TestSuite(TestParseModuleBodyItems.class));
		s.addTest(new TestSuite(TestParseSpecify.class));
		s.addTest(new TestSuite(TestParseProgramBlocks.class));
		// ErrorRecovery
		s.addTest(new TestSuite(TestParserErrorRecovery.class));
		s.addTest(new TestSuite(TestParseStruct.class));
		s.addTest(new TestSuite(TestParseTopLevelItems.class));
		s.addTest(new TestSuite(TestSystemParse.class));
		s.addTest(new TestSuite(TestTypeDeclarations.class));
		
		s.addTest(new TestSuite(TestParserSVStdExamples.class));
		s.addTest(new TestSuite(TestParseAssertions.class));
		s.addTest(new TestSuite(TestParseAttributes.class));
		s.addTest(new TestSuite(TestParseBind.class));
		s.addTest(new TestSuite(TestParseCovergroups.class));
		s.addTest(new TestSuite(TestTaskTags.class));
		
		return s;
	}

	public static void runTest(String testname, String data, String exp_items[]) throws SVParseException {
		LogHandle log = LogFactory.getLogHandle(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		InputStream in = null;
		try {
			URL url = SVCoreTestsPlugin.getDefault().getBundle().getEntry(data);
			in = url.openStream();
		} catch (IOException e) {
			TestCase.fail("Failed to open " + data + ": " + e.getMessage());
		}
		
		SVDBFile file = SVDBTestUtils.parse(log, in, data, markers).second();
		
		try {
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		TestCase.assertEquals(0, markers.size());
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		
		LogFactory.removeLogHandle(log);
	}

	public static void runTestStrDoc(
			String			testname,
			String			doc,
			String			exp_items[]) {
		runTestStrDoc(testname, doc, SVLanguageLevel.SystemVerilog, exp_items);
	}
	
	public static void runTestStrDoc(
			String			testname,
			String			doc,
			SVLanguageLevel	language_level,
			String			exp_items[]) {
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		LogHandle log = LogFactory.getLogHandle(testname);
		SVDBFile file = SVDBTestUtils.parse(log, language_level, doc, testname, markers);

		for (SVDBMarker m : markers) {
			log.debug("[MARKER] " + m.getMessage());
		}
		TestCase.assertEquals(0, markers.size());
		SVDBTestUtils.assertFileHasElements(file, exp_items);
	}


}
