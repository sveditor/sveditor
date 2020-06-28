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


package net.sf.sveditor.core.tests.indent;

import junit.framework.TestCase;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.indent.SVIndentToken;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class TestIndentScanner extends TestCase {
	
	public void testIsStartLine() {
		String content =
			"/****************************************************************************\n" +
			" * my_component1.svh\n" +
			" ****************************************************************************/\n" +
			"`ifndef INCLUDED_my_component1_svh\n" +
			"`define INCLUDED_my_component1_svh\n" +
			"\n" +
			"class my_component1 extends ovm_component;\n" +
			"	\n" +	
			"function void foobar();\n" +
			"		\n" +
			"	endfunction\n" +
			"\n";
		boolean start_line[] = {
			true,  // comment
			true,  // ifndef
			false, // INCLUDED_
			true,  // define
			false, // INCLUDED_
			true,  // blank line
			true,  // class
			false, // my_component1
			false, // extends
			false, // ovm_component
			false, // ;
		};
		boolean end_line[] = {
			true,  // comment
			false, // ifndef
			true,  // INCLUDED_
			false, // define
			true,  // INCLUDED_
			true,  // blank line
			false, // class
			false, // my_component1
			false, // extends
			false, // ovm_component
			true,  // ;
		};
		LogHandle log = LogFactory.getLogHandle("testIsStartLine");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(new StringBuilder(content)));
		
		
		for (int i=0; i<start_line.length; i++) {
			SVIndentToken tok = scanner.next();
			log.debug("tok: isStartLine=" + tok.isStartLine() + " isEndLine=" +
					tok.isEndLine() + " value=" + tok.getImage());
			
			assertEquals("Expected token " + tok.getImage() + " to start line", 
					start_line[i], tok.isStartLine());
			assertEquals("Expected token " + tok.getImage() + " to end line", 
					end_line[i], tok.isEndLine());
		}
		LogFactory.removeLogHandle(log);
	}

	public void testLeadingWhitespace() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"\n" +																					// 6
			"	class my_component1 extends ovm_component;\n" +										// 7
			"		\n" +																			// 8
			"function void foobar();\n" +															// 9
			"a = 5;\n" +
			"	endfunction\n" +
			"\n";
		LogHandle log = LogFactory.getLogHandle("testLeadingWhitespace");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(new StringBuilder(content)));
		

		SVIndentToken tok;
		
		while ((tok = scanner.next()) != null) {
			if (tok.getImage().equals("class")) {
				log.debug("Leading whitespace: \"" + tok.getLeadingWS() + "\"");
			}
		}
		LogFactory.removeLogHandle(log);
	}
	
	public void testMultiEmptyLines() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																					// 6
			"			\n" +																					// 7
			"	class my_component1 extends ovm_component;\n" +										// 8
			"		\n" +																			// 9
			"function void foobar();\n" +															// 10
			"a = 5;\n" +
			"	endfunction\n" +
			"\n";

		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(content));
		

		SVIndentToken tok;
		
		while ((tok = scanner.next()) != null && !tok.getImage().equals("`define")) { }
		tok = scanner.next(); // INCLUDED_ ...
		tok = scanner.next();
		assertEquals("Expect one tab", "	", tok.getLeadingWS());
		tok = scanner.next();
		assertEquals("Expect three tabs", "			", tok.getLeadingWS());
	}

	public void testStringWithEmbeddedCtrl() {
		String content =
			"/****************************************************************************\n" +		// 1
			" * my_component1.svh\n" +																// 2
			" ****************************************************************************/\n" +	// 3
			"`ifndef INCLUDED_my_component1_svh\n" +												// 4
			"`define INCLUDED_my_component1_svh\n" +												// 5
			"	\n" +																					// 6
			"			\n" +																					// 7
			"	class my_component1 extends ovm_component;\n" +										// 8
			"		\n" +																			// 9
			"		function void foobar();\n" +															// 10
			"			$psprintf(\"Hello World\\n    Testing %0d\\n\", a);\n" +
			"		endfunction\n" +
			"\n";

		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(content));
		
		SVIndentToken tok;
		
		while ((tok = scanner.next()) != null && !tok.getImage().equals("$psprintf")) { }
		tok = scanner.next(); // (
		tok = scanner.next();
		
		assertEquals("Check for expected full-string token",
				"\"Hello World\\n    Testing %0d\\n\"",
				tok.getImage());
	}
}
