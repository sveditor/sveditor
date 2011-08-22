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


package net.sf.sveditor.core.tests.parser;

import junit.framework.TestSuite;

public class ParserTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ParserTests");
		s.addTest(new TestSuite(TestLexer.class));
		s.addTest(new TestSuite(TestParseBehavioralStmts.class));
		s.addTest(new TestSuite(TestParseClassBodyItems.class));
		s.addTest(new TestSuite(TestParseDataTypes.class));
		s.addTest(new TestSuite(TestParseExpr.class));
		s.addTest(new TestSuite(TestParseFunction.class));
		s.addTest(new TestSuite(TestParseInterfaceBodyItems.class));
		// LineNumbers
		s.addTest(new TestSuite(TestParseLineNumbers.class));
		s.addTest(new TestSuite(TestParseModuleBodyItems.class));
		s.addTest(new TestSuite(TestParseProgramBlocks.class));
		// ErrorRecovery
		s.addTest(new TestSuite(TestParserErrorRecovery.class));
		s.addTest(new TestSuite(TestParseStruct.class));
		s.addTest(new TestSuite(TestParseTopLevelItems.class));
		s.addTest(new TestSuite(TestSystemParse.class));
		s.addTest(new TestSuite(TestTypeDeclarations.class));
		
		return s;
	}
	

}
