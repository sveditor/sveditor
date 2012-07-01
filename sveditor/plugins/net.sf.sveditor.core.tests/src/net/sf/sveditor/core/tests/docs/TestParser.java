package net.sf.sveditor.core.tests.docs;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import junit.framework.TestCase ;

public class TestParser extends TestCase {
	
	boolean fDebug = false ;
	private LogHandle fLog ;
	
	public TestParser() {
		fLog = LogFactory.getLogHandle("TestParser") ;
	}
	
	public void testBasicClassTopic() throws Exception {
		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "" 
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		runTest(commentLines, expTopics) ;
		
	}

	private void runTest(String commentLines[], Set<DocTopic> expTopics) throws Exception {
		
		if(fDebug) {
			logComment("Parsing comment", commentLines) ;
		}
		
		IDocCommentParser parser = new DocCommentParser() ;
		
		Set<DocTopic> actDocTopics = new HashSet<DocTopic>() ;
		
		parser.parseComment(commentLines, actDocTopics) ;
		
		fLog.debug(ILogLevel.LEVEL_OFF, "Done!") ;
		
		
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
