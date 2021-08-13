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
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package org.eclipse.hdt.sveditor.core.tests.docs;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.docs.DocCommentParser;
import org.eclipse.hdt.sveditor.core.docs.DocTopicManager;
import org.eclipse.hdt.sveditor.core.docs.IDocCommentParser;
import org.eclipse.hdt.sveditor.core.docs.IDocTopicManager;
import org.eclipse.hdt.sveditor.core.docs.model.DocTopic;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

import junit.framework.TestCase;

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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
		expTopics.add(classDocTopic) ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
			    "More stuff following header"
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p><ul><li>bullet 1</li><li>bullet 2</li><li>bullet 3</li></ul>") ;
		classDocTopic.setSummary("Description of the ubus_env class") ;
		
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
	public void testDefinitionList() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "",
			    "	First  - This is the first item.",
			    "	Second - This is the second item.",
			    "         	 This is more of the second item.",
			    "	Third  - This is the third item.",
			    "	This is more of the third item.",
			    "",
 			    "	Some text after the definition list."
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class</p>"
				              +"<dl><de>	First</de>" 
							  	+"<dd>This is the first item.</dd>"
							  		+"<de>	Second</de>"
							    +"<dd>This is the second item. 	 This is more of the second item.</dd>"
							     	+"<de>	Third</de>"
							    +"<dd>This is the third item. 	This is more of the third item.</dd>"
							  +"</dl>"
							  +"<p>	Some text after the definition list.</p>") ;
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <b>bold</b> text</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <b>bold</b> text") ;
		expTopics.add(classDocTopic) ;
		
		runTest(commentLines, expTopics) ;
		
	}
		
	public void testItalics() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: ubus_env",
			    "",
			    "Description of the ubus_env class",
			    "with some ~italic~ text",
			    "",
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
		classDocTopic.setBody("<p>Description of the ubus_env class with some <i>italic</i> text</p>") ;
		classDocTopic.setSummary("Description of the ubus_env class with some <i>italic</i> text") ;
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env", "class", "class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
		
		DocTopic classDocTopic = new DocTopic("ubus_env","class","class") ;
		
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
//		fDebug = true ;
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
		
		DocTopic titleTopic = new DocTopic("This is the page title","title","title") ;
		
		titleTopic.setBody("<p>this is a description of the page</p>") ;
		titleTopic.setSummary("this is a description of the page") ;
		
		expTopics.add(titleTopic) ;
		
		expTopics.add( new DocTopic("classA","class","class")) ;
		expTopics.add( new DocTopic("classB","class","class")) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
		
	public void testBasicLink() throws Exception {
//		fDebug = true ;
		String commentLines[] =  {
			    "",
			    "CLASS: classA",
			    "",
			    " This is classA",
			    "",
			    " There is a <classB> under it.",
			    " Here is another <classB>.",
			    "",
			    "CLASS: classB",
			    "" 
		} ;

		Set<DocTopic> expTopics = new HashSet<DocTopic>() ;
		
		DocTopic classA = new DocTopic("classA","class","class") ;
		classA.setBody(
				"<p>This is classA</p>" +
				"<p>There is a <link target=\"classB\" name=\"classB\" original=\"&lt; classB &gt;\"> under it. " +
				"Here is another <link target=\"classB\" name=\"classB\" original=\"&lt; classB &gt;\">.</p>") ;
		classA.setSummary("This is classA") ;
		
		expTopics.add(classA) ;
		expTopics.add( new DocTopic("classB","class","class")) ;
		
		runTest(commentLines, expTopics) ;
		
	}
	
		
	private void runTest(String commentLines[], Set<DocTopic> expTopics) throws Exception {
		
		if(fDebug) {
			logComment("Parsing comment", commentLines) ;
		}
		
		IDocTopicManager docTopicMgr = new DocTopicManager() ;
		
		IDocCommentParser parser = new DocCommentParser(docTopicMgr) ;
		
		List<DocTopic> actDocTopics = new ArrayList<DocTopic>() ;
		
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
