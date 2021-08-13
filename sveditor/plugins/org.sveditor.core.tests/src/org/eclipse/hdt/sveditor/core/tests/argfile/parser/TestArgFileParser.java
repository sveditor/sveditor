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
package org.sveditor.core.tests.argfile.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.argfile.parser.SVArgFileLexer;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import org.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import org.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import org.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import org.sveditor.core.db.argfile.SVDBArgFileStmt;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.parser.SVParseException;
import org.sveditor.core.scanutils.ITextScanner;
import org.sveditor.core.scanutils.StringTextScanner;

import junit.framework.TestCase;
import org.sveditor.core.tests.utils.TestUtils;

public class TestArgFileParser extends TestCase {
	private File				fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		if (fTmpDir != null && fTmpDir.isDirectory()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testOptionLexer() throws SVParseException {
		String testname = "testOptionLexer";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"-f /tools/usr/dir/file.f\n" +
				"";
		ITextScanner scanner = new StringTextScanner(content);
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, scanner);

		while (lexer.peek() != null) {
			log.debug("Token: \"" + lexer.getImage() + "\"");
			lexer.consumeToken();
		}
	}
	
	public void testStringArguments() throws SVParseException {
		String testname = "testOptionLexer";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"\"This is a string\"\"and this is another\"\n" +
				"-f /tools/usr/dir/file.f\n" +
				"";
		ITextScanner scanner = new StringTextScanner(content);
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, scanner);

		while (lexer.peek() != null) {
			log.debug("Token: \"" + lexer.getImage() + "\"");
			lexer.consumeToken();
		}

	}
	
	public void testPlusArgs() throws SVParseException {
		String testname = "testPlusArgs";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"+define+foo=bar +my_plusarg=bar\n" +
				"";
		ITextScanner scanner = new StringTextScanner(content);
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, scanner);

		while (lexer.peek() != null) {
			log.debug("Token: \"" + lexer.getImage() + "\"");
			lexer.consumeToken();
		}

	}

	public void testIncOpts() throws SVParseException {
		String testname = "testIncOpts";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"+incdir+/tools/include // Questa/VCS format\n" +
				"-Incdir /tools/include2 // NCSim format\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, new SVDBArgFileStmt[] {
				new SVDBArgFileIncDirStmt("/tools/include"),
				new SVDBArgFileIncDirStmt("/tools/include2")
		});
	}
	
	public void testDefOpts() throws SVParseException {
		String testname = "testDefOpts";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"+define+bar1=baz // Questa/VCS format\n" +
				"+define+foo1 // Questa/VCS format\n" +
				"-defi bar2=baz // NCSim format\n" +
				"-define foo2 // NCSim format\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, new SVDBArgFileStmt[] {
				new SVDBArgFileDefineStmt("bar1", "baz"),
				new SVDBArgFileDefineStmt("foo1", null),
				new SVDBArgFileDefineStmt("bar2", "baz"),
				new SVDBArgFileDefineStmt("foo2", null),
		});
	}

	public void testArgFileInc() throws SVParseException {
		String testname = "testArgFileInc";
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"-f /tools/argfiles/argfile1.f\n" +
				"-file /tools/argfiles/argfile2.f\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, new SVDBArgFileStmt[] {
				new SVDBArgFileIncFileStmt("/tools/argfiles/argfile1.f"),
				new SVDBArgFileIncFileStmt("/tools/argfiles/argfile2.f")
		});
	}
	
	public void testLibExtOpts() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String content =
				"+libext+.v+.sv+.svh\n" +
				"-y foo\n" +
				"+incdir+bar\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, new SVDBArgFileStmt[] {
				new SVDBArgFileSrcLibPathStmt("foo"),
				new SVDBArgFileIncDirStmt("bar")
		});
	}	
	
	public void testLocations() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle(getName());
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		String content =
				"\n" +									// 1
				"\n" +
				"+incdir+/home/mballance\n" +			// 2
				"\n" +									// 3
				"\n" +									// 4
				"/home/mballance/class1.sv\n" +			// 5
				"/home/mballance/class2.sv\n" +			// 6
				"\n" +									// 7
				"\n" +									// 8
				"/home/mballance/class3.sv\n" +			// 9
				"\n";
				

		SVDBFile file = ArgFileParserTests.parse(log, null, getName(), content, markers);
	
		// Check line numbers
		int lineno[] = new int[] {3, 6, 7, 10};
		int idx = 0;
		for (ISVDBItemBase it : file.getChildren()) {
			assertTrue(idx < lineno.length);
			assertEquals("lineno for " + it.getType(), lineno[idx], 
					SVDBLocation.unpackLineno(it.getLocation()));
			idx++;
		}
	}
}
