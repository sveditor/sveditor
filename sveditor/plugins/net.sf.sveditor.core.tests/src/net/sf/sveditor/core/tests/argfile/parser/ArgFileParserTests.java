package net.sf.sveditor.core.tests.argfile.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileStmt;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;

public class ArgFileParserTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite suite = new TestSuite();
		suite.addTestSuite(TestArgFileParser.class);
		
		return suite;
	}
	
	public static void runParserTest(
			String				testname,
			String				content,
			SVDBArgFileStmt	...	expected) throws SVParseException {
		runParserTest(null, testname, content, expected);
	}
	
	public static void runParserTest(
			ISVArgFileVariableProvider		vp,
			String							testname,
			String							content,
			SVDBArgFileStmt ...				expected) throws SVParseException {
		LogHandle log = LogFactory.getLogHandle(testname);
	
		InputStream in = new StringInputStream(content);
		SVArgFilePreProcessor pp = new SVArgFilePreProcessor(
				in, testname, vp);
		
		SVArgFilePreProcOutput pp_out = pp.preprocess();

//		ITextScanner scanner = new StringTextScanner(content);
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, pp_out);
		
		SVArgFileParser parser = new SVArgFileParser(
				"", "",
				new SVDBWSFileSystemProvider());
		parser.init(lexer, testname);
		
		SVDBFile file = new SVDBFile(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		parser.parse(file, markers);
		
		int idx = 0;
		
		for (ISVDBItemBase item : file.getChildren()) {
			SVDBArgFileStmt exp = expected[idx];
			TestCase.assertNotNull(item);
			log.debug("Item: " + SVDBItem.getName(item));
			TestCase.assertTrue("Item not instanceof ArgFileStmt", 
					(item instanceof SVDBArgFileStmt));
			TestCase.assertEquals("Item type does not match expected",
					exp.getType(), item.getType());
			
			switch (item.getType()) {
				case ArgFileIncDirStmt: {
					SVDBArgFileIncDirStmt inc = (SVDBArgFileIncDirStmt)item;
					SVDBArgFileIncDirStmt inc_e = (SVDBArgFileIncDirStmt)exp;
					log.debug("IncDir: expect " + inc_e.getIncludePath() + " receive " + inc.getIncludePath());
					TestCase.assertEquals(inc_e.getIncludePath(), inc.getIncludePath());
					} break;

				case ArgFileDefineStmt: {
					SVDBArgFileDefineStmt def = (SVDBArgFileDefineStmt)item;
					SVDBArgFileDefineStmt def_e = (SVDBArgFileDefineStmt)exp;
					log.debug("Define: expect " + def_e.getKey() + "=" + def_e.getValue() + 
							" receive " + def.getKey() + "=" + def.getValue());
					TestCase.assertEquals(def_e.getKey(), def.getKey());
					TestCase.assertEquals(def_e.getValue(), def.getValue());
					} break;
					
				case ArgFilePathStmt: {
					SVDBArgFilePathStmt path = (SVDBArgFilePathStmt)item;
					SVDBArgFilePathStmt path_e = (SVDBArgFilePathStmt)exp;
					
					log.debug("Path: expect " + path_e.getPath() + 
							" receive " + path.getPath());
					TestCase.assertEquals(path_e.getPath(), path.getPath());
					} break;
					
				case ArgFileIncFileStmt: {
					SVDBArgFileIncFileStmt inc = (SVDBArgFileIncFileStmt)item;
					SVDBArgFileIncFileStmt inc_e = (SVDBArgFileIncFileStmt)exp;
					
					log.debug("IncFile: expect " + inc_e.getPath() + 
							" receive " + inc.getPath());
					
					TestCase.assertEquals(inc_e.getPath(), inc.getPath());
					} break;
					
					
				default: {
					TestCase.fail("Unrecognized argument-file statement: " + item.getType());
				}
			}
			idx++;
		}
		
		TestCase.assertEquals("Wrong number of items in parse tree",
				expected.length, idx);
		LogFactory.removeLogHandle(log);
	}

}
