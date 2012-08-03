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

public class TestContentAssistInterface extends TestCase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistInterfaceBasics() {
		String testname = "testContentAssistInterfaceBasics";
		LogHandle log = LogFactory.getLogHandle(testname);
		String doc1 =
			"interface foo_if;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endinterface\n" +
			"\n" +
			"\n" +
			"task my_class::my_task();\n" +
			"	virtual foo_if			m_foo_if;\n" +
			"	m_foo_if.<<MARK>>\n" +
			"endtask\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
				
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
		
		ContentAssistTests.validateResults(new String[] {"AAAA", "AABB", "BBCC"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testInterfaceTaskVarAssist() {
		String testname = "testInterfaceTaskVarAssist";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	task f;\n" +
				"		AA<<MARK>>\n" +
				"	endtask\n" +
				"endinterface\n"
				;
			
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
			
			/*
			Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc1);
			TextTagPosUtils tt_utils = ini.second();
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
			
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
			 */
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			TestCompletionProcessor cp = new TestCompletionProcessor(testname, file, 
					new FileIndexIterator(file));
			
			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
			LogFactory.removeLogHandle(log);
	}

	public void testInterfaceModuleFieldAssist() {
		String testname = "testInterfaceModuleFieldAssist";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top;\n" +
				"	i1		ifc_if();\n" +
				"\n" +
				"	submodule s1(" +
				"		.p1(if<<MARK>>\n" +
				"	);\n" +
				"endmodule"
				;
			
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
			
			/*
			Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc1);
			TextTagPosUtils tt_utils = ini.second();
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
			
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
			 */
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			TestCompletionProcessor cp = new TestCompletionProcessor(testname, file, 
					new FileIndexIterator(file));
			
			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			ContentAssistTests.validateResults(new String[] {"ifc_if"}, proposals);
			LogFactory.removeLogHandle(log);
	}
	
	public void testInterfaceModulePortAssist() {
		String testname = "testInterfaceModulePortAssist";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 = 
				"interface i1(input clk, input rst);\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top;\n" +
				"	i1		ifc_if();\n" +
				"\n" +
				"	submodule s1(" +
				"		.p1(ifc_if.c<<MARK>>\n" +
				"	);\n" +
				"endmodule"
				;
			
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
			
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			TestCompletionProcessor cp = new TestCompletionProcessor(testname, file, 
					new FileIndexIterator(file));
			
			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			ContentAssistTests.validateResults(new String[] {"clk"}, proposals);
			LogFactory.removeLogHandle(log);
	}	
	
	public void testInterfaceModportModuleField() {
		String testname = "testInterfaceModportModuleField";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	modport foo(input AAAA, AABB, BBBB);\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top;\n" +
				"	i1		ifc_if();\n" +
				"\n" +
				"	submodule s1(" +
				"		.p1(ifc_if.f<<MARK>>\n" +
				"	);\n" +
				"endmodule"
				;
			
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
			
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			TestCompletionProcessor cp = new TestCompletionProcessor(testname, file, 
					new FileIndexIterator(file));
			
			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			ContentAssistTests.validateResults(new String[] {"foo"}, proposals);
			LogFactory.removeLogHandle(log);
	}
	
	public void testInterfaceModportModulePort() {
		String testname = "testInterfaceModportModulePort";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	modport foo(input AAAA, AABB, BBBB);\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top(" +
				"	i1.foo		foo_p" +
				"	);\n" +
				"\n" +
				"	initial begin\n" +
				"		foo_p.AA<<MARK>>\n" +
				"	end\n" +
				"endmodule"
				;
			
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
			
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			TestCompletionProcessor cp = new TestCompletionProcessor(testname, file, 
					new FileIndexIterator(file));
			
			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
			LogFactory.removeLogHandle(log);
	}
	
	public void testInterfaceModportModulePort_1() {
		String testname = "testInterfaceModportModulePort";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc1 = 
				"interface i1();\n" +
				"\n" +
				"\n" +
				"	int			AAAA;\n" +
				"	int			AABB;\n" +
				"	int			BBBB;\n" +
				"\n" +
				"	modport foo(input AAAA, AABB, BBBB);\n" +
				"\n" +
				"endinterface\n" +
				"\n" +
				"module top(" +
				"	i1.foo		p_foo" +
				"	);\n" +
				"\n" +
				"	initial begin\n" +
				"		p_<<MARK>>\n" +
				"	end\n" +
				"endmodule"
				;
			
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
			ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
			
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			TestCompletionProcessor cp = new TestCompletionProcessor(testname, file, 
					new FileIndexIterator(file));
			
			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			ContentAssistTests.validateResults(new String[] {"p_foo"}, proposals);
			LogFactory.removeLogHandle(log);
	}
	
}


