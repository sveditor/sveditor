package net.sf.sveditor.core.tests.docs;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.docs.DocCommentCleaner;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase ;

public class TestCleaner extends TestCase {
	
	boolean fDebug = false ;
	private LogHandle fLog ;
	
	public TestCleaner() {
		fLog = LogFactory.getLogHandle("TestCleaner") ;
	}
	
	public void testBoxRemoval() throws Exception {
//		fDebug = true ;
		String comment [] = {
			  "",
			  "------------------------------------",	// Entire line should be removed
			  "class: the_class   ",					// Only trailing white should be removed (spaces)
			  "------------------------------------",	// Entire line should be removed even with white space at end
			  "class_with_tabs: the_class		",		// Only trailing white should be removed (tabs)
			  "class_with_tabs: the_class	  	",		// Only trailing white should be removed (tabs and spaces)
			  "+++++++++++++++++++++++++++",
			  "+++++++++++++++++++++++++++   ",
			  "  ",
			  "" } ; 
		String cleanedContent[] = {
			  "",
			  "",
			  "class: the_class" ,
			  "",
			  "class_with_tabs: the_class",
			  "class_with_tabs: the_class",
			  "",
			  "",
			  "",
			  "" } ;
		runTest("testBoxRemoval", comment, cleanedContent) ;
		
	}

	public void testLeadingCommentMarkRemoval() throws Exception {
		fDebug = true ;
		String comment [] = {
			  "*",
			  "*",										// Entire line should be removed
			  "* class: the_class   ",					// Only trailing white should be removed (spaces)
			  "*",										// Entire line should be removed even with white space at end
			  "* class_with_tabs: the_class		",		// Only trailing white should be removed (tabs)
			  "* class_with_tabs: the_class	  	",		// Only trailing white should be removed (tabs and spaces)
			  "*",
			  "*",
			  "*",
			  "*" } ; 
		String cleanedContent[] = {
			  "",
			  "",
			  " class: the_class" ,
			  "",
			  " class_with_tabs: the_class",
			  " class_with_tabs: the_class",
			  "",
			  "",
			  "",
			  "" } ;
		runTest("testLeadingCommentMarkRemoval", comment, cleanedContent) ;
	}
	
	public void testSVPreProc_1() throws Exception {
		String testname = "testSVPreProc_1";
		String doc = 
				"/**\n" +
				" * CLASS: my_class\n" +
				" * This is the class description\n" +
				" *\n" +
				" */\n" +
				" class my_class;\n" +
				" endclass\n"
				;
		Tuple<SVDBFile, SVDBFile> r = SVDBTestUtils.parsePreProc(doc, testname, false);
		
		SVDBFile pp_file = r.first();
		SVDBDocComment dc = null;
		for (ISVDBChildItem c : pp_file.getChildren()) {
			if (c.getType() == SVDBItemType.DocComment) {
				dc = (SVDBDocComment)c;
			}
		}
	
		assertTrue(dc.getRawComment().contains("CLASS: my_class"));
	}
	
	public void testSVPreProc_2() throws Exception {
		String testname = "testSVPreProc_2";
		String doc = 
				"//\n" +
				"// CLASS: my_class\n" +
				"// This is the class description\n" +
				"//\n" +
				"//\n" +
				" class my_class;\n" +
				" endclass\n"
				;
		Tuple<SVDBFile, SVDBFile> r = SVDBTestUtils.parsePreProc(doc, testname, false);
		
		SVDBFile pp_file = r.first();
		SVDBDocComment dc = null;
		for (ISVDBChildItem c : pp_file.getChildren()) {
			if (c.getType() == SVDBItemType.DocComment) {
				dc = (SVDBDocComment)c;
			}
		}
	
		assertTrue(dc.getRawComment().contains("CLASS: my_class"));
	}
	
	private void runTest(String string, String comment[], String expCleanedComment[]) throws Exception {
		
		SVCorePlugin.getDefault().enableDebug(fDebug);
		
    	if(comment.length != expCleanedComment.length) {
    		throw(new Exception("Len of input lines(" + comment.length + ")"
    							+ " different from given expected lines length(" + expCleanedComment.length + ")")) ;
    	}
		
		if(fDebug) {
			logComment("Cleaning comment",comment);
			logComment("Expecting comment", expCleanedComment) ;
		}
		
		DocCommentCleaner.clean(comment);
		
		if(fDebug) {
			logComment("Cleaned comment", comment) ;
		}
		
		for(int lineNum=0 ; lineNum < comment.length ; lineNum++) {
			assertEquals(String.format("Mismatch line[%03d]",lineNum), expCleanedComment[lineNum], comment[lineNum]) ;
		}
		
		
	}

	private void logComment(String msg, String[] lines) {
		fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| " + msg ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------------") ;
		for(int lineNum=0 ; lineNum<lines.length ; lineNum++) {
		fLog.debug(ILogLevel.LEVEL_OFF, String.format("|[%03d]",lineNum) + lines[lineNum] + "<end>") ;
		}
	}
	

}
