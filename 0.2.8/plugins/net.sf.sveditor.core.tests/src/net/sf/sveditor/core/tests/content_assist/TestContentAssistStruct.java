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

import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.TextTagPosUtils;

public class TestContentAssistStruct extends TestCase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructTypedef() {
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
		SVCorePlugin.getDefault().enableDebug(true);
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (SVDBItem it : file.getItems()) {
			System.out.println("    it: " + it.getType() + " " + it.getName());
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
	}

	/**
	 * Test that content assist on struct module ports works
	 */
	public void testContentAssistStructModuleInput() {
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
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (SVDBItem it : file.getItems()) {
			System.out.println("    it: " + it.getType() + " " + it.getName());
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
	}

	/**
	 * Test that content assist on struct module ports works
	 * In this case, ensure that a parse error from the missing
	 * semicolon doesn't throw off content assist
	 */
	public void testContentAssistStructModuleInputModuleScope() {
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
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (SVDBItem it : file.getItems()) {
			System.out.println("    it: " + it.getType() + " " + it.getName());
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
	}

	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructInClassTypedef() {
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
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (SVDBItem it : file.getItems()) {
			System.out.println("    it: " + it.getType() + " " + it.getName());
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field"}, proposals);
	}

	/**
	 * Test that basic macro content assist works
	 */
	public void testContentAssistStructField() {
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
				
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (SVDBItem it : file.getItems()) {
			System.out.println("    it: " + it.getType() + " " + it.getName());
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"my_int_field", "my_bit_field", 
				"my_logic_field", "my_logic_queue"}, proposals);
	}

}
