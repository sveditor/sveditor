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

public class TestContentAssistClass extends TestCase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistExternTaskClass() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistExternTaskClass");
		SVCorePlugin.getDefault().enableDebug(true);
		String doc1 =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"class my_class2;\n" +
			"	foobar		m_field2;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	m_<<MARK>>\n" +
			"endtask\n"
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
		
		ContentAssistTests.validateResults(new String[] {"m_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testIgnoreForwardDecl() {
		String testname = "testIgnoreForwardDecl";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"typedef class foobar;\n" +
			"\n" +
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	task my_task();\n" +
			"		foobar v;\n" +
			"\n" +
			"		v.A<<MARK>>\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testIgnoreNullStmt() {
		String testname = "testIgnoreNullStmt";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"typedef class foobar;\n" +
			"\n" +
			"class foobar;\n" +
			"	int		AAAA;;\n" +
			"	int		AABB;\n" +
			"	constraint c {\n" +
			"	};\n" + // The ';' in this case is a null statement
			"	;\n" +
			"	;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	task my_task();\n" +
			"		foobar v;\n" +
			"\n" +
			"		v.A<<MARK>>\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testContentAssistExternTaskClassField() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistExternTaskClassField");
		String doc1 =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	m_field.AA<<MARK>>\n" +
			"endtask\n"
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
		
		ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistSuperSuperClass() {
		String testname = "testContentAssistSuperSuperClass";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends super_2;\n" +
			"\n" +
			"	function void build();\n" +
			"		super.<<MARK>>\n" +
			"	endfunction" +
			"endclass\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		/*
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}
		 */

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(new String[] {
				"AAAA", "AABB",
				"BBBB", "BBCC",
				"CCCC", "CCDD"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistSuperClass_1() {
		String testname = "testContentAssistSuperClass_1";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"module foo;\n" +
			"endmodule\n" +
			"\n" +
			"function void bar;\n" +
			"endfunction\n" +
			"\n" +
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends <<MARK>>\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(new String[] {
				"base", "super_1", "super_2"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testContentAssistBaseClass() {
		String testname = "v";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends s<<MARK>>\n" +
			"\n" +
			"	function void build();\n" +
			"		super.build();\n" +
			"	endfunction" +
			"endclass\n" +
			"\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"super_1", "super_2"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistBaseClassEOF() {
		String testname = "testContentAssistBaseClassEOF";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends s<<MARK>>"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));
		
		log.debug("Cursor line: " + tt_utils.getLineMap().get("MARK"));
		log.debug("Cursor pos: " + tt_utils.getPosMap().get("MARK"));
		log.debug("Content: \"" + scanner.getContent() + "\"");
		log.debug("Content length: " + scanner.getContent().length());
//		int ch = scanner.get_ch();
//		log.debug("Current char: " + (char)ch);
//		scanner.unget_ch(ch);

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"super_1", "super_2"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testContentAssistOnlyTopNew_1() {
		String testname = "testContentAssistOnlyTopNew_1";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"	function new(int p1, int p2, int p3);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"	function new(int p1, int p2);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends super_2 #(5);\n" +
			"\n" +
			"	function void build();\n" +
			"		super.build();\n" +
			"	endfunction" +
			"\n" +
			"	function new(int p1);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		my_class f = n<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"new"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistOnlyTopNew_2() {
		String testname = "testContentAssistOnlyTopNew_2";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	int		BBBB;\n" +
			"	int		BBCC;\n" +
			"	function new(int p1, int p2, int p3);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_2 #(int T) extends super_1;\n" +
			"	int		CCCC;\n" +
			"	int		CCDD;\n" +
			"	function new(int p1, int p2);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class my_class extends super_2 #(5);\n" +
			"\n" +
			"	function void build();\n" +
			"		super.build();\n" +
			"	endfunction" +
			"\n" +
			"	function new(int p1);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"module top;\n" +
			"	function foo;\n" +
			"		my_class f = n<<MARK>>\n" +
			"	endfunction\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"new"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testStaticTypeAssist_1() {
		String testname = "testStaticTypeAssist_1";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_ba<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"m_base"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testStaticTypeAssist_2() {
		String testname = "testStaticTypeAssist_2";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base.AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testStaticTypeAssist_3() {
		String testname = "testStaticTypeAssist_3";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	static int		AAAA;\n" +
			"	static int		AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testStaticTypeAssist_4() {
		String testname = "testStaticTypeAssist_4";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	static base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"AAAA"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	// Ensure that the expression-traversal code correctly
	// excludes non-static fields when referenced in a static way
	public void testStaticTypeAssist_5() {
		String testname = "testStaticTypeAssist_5";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	base			m_base;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::m_base::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {}, proposals);
		LogFactory.removeLogHandle(log);
	}	

	// Ensure that content assist is able to traverse typedefs
	public void testStaticTypeAssist_6() {
		String testname = "testStaticTypeAssist_6";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base;\n" +
			"	static function int create();\n" +
			"	endfunction\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	typedef base		type_id;\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		super_1::type_id::cr<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(new String[] {"create"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testParameterizedTypeAssist_1() {
		String testname = "testStaticTypeAssist_1";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base #(int A=1, int B=2);\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		base#(1,4)::AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"AAAA"}, proposals);
		LogFactory.removeLogHandle(log);
	}	
	
	public void testParameterizedTypeAssist_2() {
		String testname = "testStaticTypeAssist_2";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 =
			"class base #(int A=1, int B=2);\n" +
			"	static int		AAAA;\n" +
			"	int				AABB;\n" +
			"	function new(int p1, int p2, int p3, int p4);\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		base#(1,4) c;" +
			"		c.AA<<MARK>>\n" +
			"	end\n" +
			"endmodule\n" +
			"\n"
			;
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(
				new String[] {"AABB"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistIgnoreBaseClassTF() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistIgnoreBaseClassTF");
		String doc1 =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"class my_class2;\n" +
			"	foobar		m_field2;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	m_<<MARK>>\n" +
			"endtask\n"
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
		
		ContentAssistTests.validateResults(new String[] {"m_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}
	
	public void testContentAssistOnlyTopTF_1() {
		String testname = "testContentAssistOnlyTopTF_1";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	function AABB();\n" +
			"	endfunction\n" +
			"\n" +
			"	function BBAA();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	function AABB();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"module top;\n" +
			"	function foo;\n" +
			"		super_1 f;\n" +
			"		f.AA<<MARK>>\n" +
			"	endfunction\n" +
			"endmodule\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(testname, doc, 
				"AAAA", "AABB");
	}

	public void testContentAssistOnlyTopTF_2() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class base;\n" +
			"	virtual task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	virtual function AABB();\n" +
			"	endfunction\n" +
			"\n" +
			"	virtual function BBAA();\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n" +
			"class super_1 extends base;\n" +
			"	virtual task AAAA();\n" +
			"	endtask\n" +
			"\n" +
			"	virtual function AABB();\n" +
			"		AAA<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n" +
			"\n"
			;
		
		ContentAssistTests.runTest(testname, doc, 
				"AAAA");
	}
}


