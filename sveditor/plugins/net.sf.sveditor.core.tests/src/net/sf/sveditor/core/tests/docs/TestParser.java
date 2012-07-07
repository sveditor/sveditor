/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.tests.docs;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.docs.model.DocClassItem;
import net.sf.sveditor.core.docs.model.DocTopic;
import net.sf.sveditor.core.docs.model.DocSectionItem;
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
		
		expTopics.add(new DocClassItem("ubus_env")) ;
		
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class") ;
		
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}

	public void testSimplClassTopicWithHeaderLine() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "" ,
			    "This is a header line:",
			    "",
			    "More stuff following header"
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>"
								+"<h4 class=CHeading>This is a header line</h4>"
								+"<p>More stuff following header</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class") ;
		
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class. The first para continues here</p><p>The second starts and continues here</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class. ") ;
		
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p><ul><li>bullet 1</li><li>bullet 2</li><li>bullet 3</li></ul>") ;
		classDocTopic.setSummary("Description of the ubus_env class") ;
		
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <b>bold</b> text</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <b>bold</b> text") ;
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <b>bold text</b></p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <b>bold text</b>") ;
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <u>underlined</u> text</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <u>underlined</u> text") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testUnderlineMultiWord() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some _underlined_text_",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <u>underlined text</u></p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <u>underlined text</u>") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testUnderlineMultiWordWithWS() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some _underlined text_",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <u>underlined text</u></p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <u>underlined text</u>") ;
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
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>"
								+"<blockquote><pre>"
									+"this is some code\n"
								    +"this is more code\n"
									+"more code"
								+"</pre></blockquote>") ;
		classDocTopic.setSummary("Description of the ubus_env class") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	public void testClassTopicWithCodeBlockCarrot() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "",
			    "> this is some code",
			    "> this is more code", 
			    "> more code"
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocClassItem("ubus_env") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>"
								+"<blockquote><pre>"
									+"this is some code\n"
								    +"this is more code\n"
									+"more code"
								+"</pre></blockquote>") ;
		classDocTopic.setSummary("Description of the ubus_env class") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	public void testTitleAndClasses() throws Exception {
		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "title: This is the page title",
			    "",
			    "this is a description of the page",
			    "", 
			    "CLASS: classA",
			    "",
			    "",
			    "CLASS: classB",
			    "" 
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic titleTopic = new DocSectionItem("This is the page title") ;
		
		titleTopic.setBody("<p>this is a description of the page</p>") ;
		titleTopic.setSummary("this is a description of the page") ;
		
		expTopics.add(titleTopic) ;
		
		expTopics.add(new DocClassItem("classA")) ;
		expTopics.add(new DocClassItem("classB")) ;
		
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
						logBody("Expecting summary:", expTopic.getSummary()) ;
						logBody("Actual summary:", actTopic.getSummary()) ;
					}
					assertEquals("Body for topic " + expTopic.getTitle() + " differs from expected",
							expTopic.getBody(), actTopic.getBody()) ;
					assertEquals("Sumamry for topic " + expTopic.getTitle() + " differs from expected",
							expTopic.getSummary(), actTopic.getSummary()) ;
					break ;
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
