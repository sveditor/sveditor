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
package net.sf.sveditor.core.tests.argfile.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;

public class TestArgFilePreProcessor extends TestCase {
	
	public void testBraceDelimitedVarExpansion() throws SVParseException {
		ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(null);
		String testname = "testBraceDelimitedVarExpansion";
		String content =
				"+define+${VARIABLE1}=${VARIABLE2}\n"
				;
		
		SVCorePlugin.setenv("VARIABLE1", "value1");
		SVCorePlugin.setenv("VARIABLE2", "value2");
	
		ArgFileParserTests.runParserTest(vp, testname, content, null,
				new SVDBArgFileStmt[] {
					new SVDBArgFileDefineStmt("value1", "value2")
				});
	}
	
	public void testNonBraceDelimitedVarExpansion() throws SVParseException {
		ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(null);
		String testname = "testNonBraceDelimitedVarExpansion";
		String content =
				"+define+$VARIABLE1=$VARIABLE2\n"
				;
		
		SVCorePlugin.setenv("VARIABLE1", "value1");
		SVCorePlugin.setenv("VARIABLE2", "value2");
	
		ArgFileParserTests.runParserTest(vp, testname, content, null,
				new SVDBArgFileStmt[] {
					new SVDBArgFileDefineStmt("value1", "value2")
				});
	}
	
	public void testNonBraceDelimitedVarExpansion2() throws SVParseException {
		ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(null);
		String testname = "testNonBraceDelimitedVarExpansion2";
		String content =
				"/tools/$VARIABLE1/$VARIABLE2\n"
				;
		
		SVCorePlugin.setenv("VARIABLE1", "value1");
		SVCorePlugin.setenv("VARIABLE2", "value2");
	
		ArgFileParserTests.runParserTest(vp, testname, content, null,
				new SVDBArgFileStmt[] {
					new SVDBArgFilePathStmt("/tools/value1/value2")
				});
	}
	
	public void testPreProcLineMap() {
		LogHandle log = LogFactory.getLogHandle(getName());
		String content =
				"\n" +
				"line2\n" +
				"line3\n" +
				"\n" +
				"\n" +
				"line4\n"
				;
		
		SVArgFilePreProcOutput pp_out = ArgFileParserTests.preprocess(log, null, getName(), content);
		
		for (int idx : pp_out.getLineMap()) {
			System.out.println("idx: " + idx);
		}
		
		int lineno = 0;
		int ch;
		while ((ch = pp_out.get_ch()) != -1) {
			/*
			int c_lineno = pp_out.getLocation().getLineNo();
			if (c_lineno != lineno) {
				lineno = c_lineno;
//				System.out.print("" + lineno + ": ");
			}
			 */
			System.out.print((char)ch);
			if (ch == '\n') {
				System.out.print("L" + pp_out.getLocation().getLineNo() + ": ");
			}
		}
	
		LogFactory.removeLogHandle(log);
	}

}
