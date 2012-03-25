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

public class TestContentAssistStruct extends TestCase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructTypedef() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistStructTypedef");
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" +
			"    int             my_int_field;\n" +
			"    bit             my_bit_field;\n" +
			"} my_struct_t;\n" +
			"\n" +
			"class my_class;\n" +
			"    my_struct_t              my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
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
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Test that content assist on struct module ports works
	 */
	public void testContentAssistStructModuleInput() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistStructModuleInput");
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" +
			"    int             my_int_field;\n" +
			"    bit             my_bit_field;\n" +
			"} my_struct_t;\n" +
			"\n" +
			"module foo_m(input my_struct_t mm);\n" +
			"\n" +
			"    function void foo();\n" +
			"        mm.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endmodule\n"
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
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Test that content assist on struct module ports works
	 * In this case, ensure that a parse error from the missing
	 * semicolon doesn't throw off content assist
	 */
	public void testContentAssistStructModuleInputModuleScope() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistStructModuleInputModuleScope");
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" +
			"    int             my_int_field;\n" +
			"    bit             my_bit_field;\n" +
			"} s;\n" +
			"\n" +
			"module foo_m(input s b);\n" +
			"\n" +
			"    b.<<MARK>>\n" +
			"endmodule\n"
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
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructInClassTypedef() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistStructInClassTypedef");
		SVCorePlugin.getDefault().enableDebug(false);
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"\n" +
			"    typedef struct {\n" +
			"        int             my_int_field;\n" +
			"        bit             my_bit_field;\n" +
			"    } my_struct_t;\n" +
			"\n" +
			"    my_struct_t              my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
				
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
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testContentAssistStructInClassTypedefRedirect() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistStructInClassTypedefRedirect");
		SVCorePlugin.getDefault().enableDebug(false);
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"\n" +
			"    typedef struct {\n" +
			"        int             my_int_field;\n" +
			"        bit             my_bit_field;\n" +
			"    } my_struct_t;\n" +
			"\n" +
			"	typedef my_struct_t my_struct_t2;\n" +
			"\n" +
			"    my_struct_t2              my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
				
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
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructField() {
		LogHandle log = LogFactory.getLogHandle("testContentAssistStructField");
		String doc1 =
			"class foobar;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"    struct {\n" +
			"        int             my_int_field;\n" +
			"        bit             my_bit_field;\n" +
			"		 logic [1:0]     my_logic_field;\n" +
			"        logic [2:0]     my_logic_queue[$];\n" +
			"    } my_struct;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_struct.my_<<MARK>>\n" +
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
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field", 
				"my_logic_field", "my_logic_queue"}, proposals);
		LogFactory.removeLogHandle(log);
	}

}
