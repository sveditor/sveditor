package net.sf.sveditor.core.tests.docs;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.docs.model.DocItemType;
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
	
	public void testEmptyClassTopic() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "" 
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		expTopics.add(new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env")) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	public void testSimplClassTopic() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "" 
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>") ;
		
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}

	public void testClassTopicWithMultiParagraphs() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class.",
			    "The first para continues here",
			    "",
			    "The second starts",
			    "and continues here"
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class. The first para continues here</p><p>The second starts and continues here</p>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	public void testClassTopicWithList() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "",
			    "- bullet 1",
			    "- bullet 2",
			    "- bullet 3"
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p><ul><li>bullet 1</li><li>bullet 2</li><li>bullet 3</li></ul>") ;
		
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	public void testBold() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some *bold* text",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <b>bold</b> text</p>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testBoldMultiWord() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some *bold text*",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <b>bold text</b></p>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testUnderline() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some _underlined_ text",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <u>underlined</u> text</p>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testUnderlineMultiWord() throws Exception {
		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some _underlined_text_",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <u>underlined text</u></p>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testClassTopicWithCodeBlock() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "",
			    "| this is some code",
			    "| this is more code", 
			    "| more code"
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env", DocItemType.Topic, "", "ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>"
								+"<blockquote><pre>"
									+"this is some code\n"
								    +"this is more code\n"
									+"more code"
								+"</pre></blockquote>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	private void runTest(String commentLines[], Set<DocTopic> expTopics) throws Exception {
		
		if(fDebug) {
			logComment("Parsing comment", commentLines) ;
		}
		
		IDocCommentParser parser = new DocCommentParser() ;
		
		Set<DocTopic> actDocTopics = new HashSet<DocTopic>() ;
		
		parser.parseComment(commentLines, actDocTopics) ;
		
		for(DocTopic expTopic: expTopics) {
			DocTopic actTopic = null ;
			for(DocTopic topic: actDocTopics) {
				if(topic.getTitle().equals(expTopic.getTitle())) {
					actTopic = topic ;
					actDocTopics.remove(topic) ;
					if(fDebug) {
						logBody("Expecting body:", expTopic.getBody()) ;
						logBody("Actual body:", actTopic.getBody()) ;
					}
					assertEquals("Body for topic " + expTopic.getTitle() + " differs from expected",
							expTopic.getBody(), actTopic.getBody()) ;
					continue ;
				}
			}
			assertNotNull("DocTopic for title(" + expTopic.getTitle() + ") not found", actTopic) ;
		}
		
		assertTrue("Unexpected topics parsed", actDocTopics.size()==0) ;
		
		fLog.debug(ILogLevel.LEVEL_OFF, "Done!") ;
		
	}

	private void logBody(String msg, String body) {
		fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| " + msg ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_OFF, body) ;
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
