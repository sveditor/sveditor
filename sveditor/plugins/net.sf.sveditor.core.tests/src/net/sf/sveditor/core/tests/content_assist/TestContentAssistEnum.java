/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.content_assist;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.TextTagPosUtils;

public class TestContentAssistEnum extends TestCase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistEnumeratorAssign() {
		String testname = "testContentAssistEnumerator";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef enum {\n" +
			"    E_ENUM_A,\n" +
			"    E_ENUM_B,\n" +
			"    _MY_ENUM_C\n" +
			"} my_enum_t;\n" +
			"\n" +
			"class my_class;\n" +
			"    my_enum_t              ab;\n" +
			"\n" +
			"    function void foo();\n" +
			"        ab = E_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"E_ENUM_A", "E_ENUM_B"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistInClassEnumDecl() {
		String testname = "testContentAssistInClassEnumDecl";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"class my_class;\n" +
			"	typedef enum {\n" +
			"		E_ENUM_A,\n" +
			"		E_ENUM_B,\n" +
			"		_MY_ENUM_C\n" +
			"	} my_enum_t;\n" +
			"    my_enum_t              ab;\n" +
			"\n" +
			"    function void foo();\n" +
			"        ab = E_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"E_ENUM_A", "E_ENUM_B"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
}
