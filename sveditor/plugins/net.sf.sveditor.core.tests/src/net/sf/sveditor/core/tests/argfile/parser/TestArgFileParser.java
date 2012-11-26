package net.sf.sveditor.core.tests.argfile.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

public class TestArgFileParser extends TestCase {
	
	public void testOptionLexer() throws SVParseException {
		String testname = "testOptionLexer";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(true);
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
		SVCorePlugin.getDefault().enableDebug(true);
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
		SVCorePlugin.getDefault().enableDebug(true);
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
		SVCorePlugin.getDefault().enableDebug(true);
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
		SVCorePlugin.getDefault().enableDebug(true);
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
		SVCorePlugin.getDefault().enableDebug(true);
		String content =
				"-f /tools/argfiles/argfile1.f\n" +
				"-file /tools/argfiles/argfile2.f\n" +
				"";
		
		ArgFileParserTests.runParserTest(testname, content, new SVDBArgFileStmt[] {
				new SVDBArgFileIncFileStmt("/tools/argfiles/argfile1.f"),
				new SVDBArgFileIncFileStmt("/tools/argfiles/argfile2.f")
		});
	}
}
