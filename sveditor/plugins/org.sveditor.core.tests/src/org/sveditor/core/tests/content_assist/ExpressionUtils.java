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
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.core.tests.content_assist;

import org.sveditor.core.StringInputStream;
import org.sveditor.core.expr_utils.SVExprContext;
import org.sveditor.core.expr_utils.SVExprScanner;
import org.sveditor.core.scanutils.StringBIDITextScanner;

import junit.framework.TestCase;
import org.sveditor.core.tests.TextTagPosUtils;

public class ExpressionUtils extends TestCase {
	
	
	/*
	public void testExtractPreTriggerPortion() {
		SVExpressionUtils expr_utils = new SVExpressionUtils(
				new SVDBFindContentAssistNameMatcher());
		
		String doc1 = 
			"class my_class;\n" +
			"    <<FIELD1>>\n" +
			"    m_data.foo_<<FIELD2>>\n" +
			"    (type'(m_data.foo().bar())).pre_<<FIELD3>>\n" +
			"endclass\n";
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		
		String pre_trigger;
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));
		pre_trigger = expr_utils.extractPreTriggerPortion(scanner);
		System.out.println("pre_trigger=\"" + pre_trigger + "\"");
		assertEquals("", pre_trigger);
		
		scanner.seek(tt_utils.getPosMap().get("FIELD2"));
		pre_trigger = expr_utils.extractPreTriggerPortion(scanner);
		System.out.println("pre_trigger=\"" + pre_trigger + "\"");
		assertEquals("m_data.foo_", pre_trigger);
		
		
		scanner.seek(tt_utils.getPosMap().get("FIELD3"));
		pre_trigger = expr_utils.extractPreTriggerPortion(scanner);
		System.out.println("pre_trigger=\"" + pre_trigger + "\"");
		assertEquals("(type'(m_data.foo().bar())).pre_", pre_trigger);
	}
	 */
	
	public void testExtractPreTriggerPortionUntriggered() {
		String content = 
		"/****************************************************************************\n" + 
        " * TmpClassPkg.sv \n" +
        " * \n" + 
        " ****************************************************************************/\n" +
        "\n" +
        "package TmpClassPkg;\n" +
        "\n" +
        "class TmpClass;\n" +
	    "    static TmpClass2  m_map[string];\n" +
        "\n" +
	    "    function new();\n" +
		"\n" +
	    "    endfunction\n" +
	    "\n" +
	    "    function void add_entry(string name);\n" +
	    "        string map_index;\n" +
	    "\n" +
	    "        map_index = get_index();\n" +
	    "        m_map[map_index] = this;\n" +
	    "\n" +
	    "        m_tr<<CA>>\n" +
	    "\n" +
	    "    endfunction\n" +
	    "\n" +
	    "\n" +
	    "endclass\n" +
	    "endpackage\n" +
	    "\n";
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(content));
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		SVExprScanner expr_scan = new SVExprScanner();
		
		scanner.seek(tt_utils.getTagPos("CA"));
		SVExprContext ctxt = expr_scan.extractExprContext(scanner, false);
		
		System.out.println("ctxt: pre=\"" + ctxt.fLeaf + "\" start=" + 
				ctxt.fStart + "\"");
	}
	
	public void testExtractExprContext() {
		SVExprScanner expr_scan = new SVExprScanner();
		
		String doc1 = 
			"class my_class;\n" +
			"    <<FIELD1>>\n" +
			"    m_data.foo_<<FIELD2>>bar;\n" +
			"    (type'(m_data.foo().bar())).pre_<<FIELD3>>\n" +
			"endclass\n";
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		System.out.println("stripped data: " + tt_utils.getStrippedData());
		
		SVExprContext ctxt;
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));
		ctxt = expr_scan.extractExprContext(scanner, false);
		
		System.out.println("ctxt: pre=\"" + ctxt.fLeaf + "\" start=" +
				ctxt.fStart + " trigger=\"" + ctxt.fTrigger + "\"");
		
		scanner.seek(tt_utils.getPosMap().get("FIELD2"));
		ctxt = expr_scan.extractExprContext(scanner, false);
		System.out.println("ctxt: pre=\"" + ctxt.fLeaf + "\" start=" +
				ctxt.fStart + " trigger=\"" + ctxt.fTrigger + "\"");

		scanner.seek(tt_utils.getPosMap().get("FIELD2"));
		ctxt = expr_scan.extractExprContext(scanner, true);
		System.out.println("ctxt: pre=\"" + ctxt.fLeaf + "\" start=" +
				ctxt.fStart + " trigger=\"" + ctxt.fTrigger + "\"");

		scanner.seek(tt_utils.getPosMap().get("FIELD3"));
		ctxt = expr_scan.extractExprContext(scanner, false);
		System.out.println("ctxt: pre=\"" + ctxt.fLeaf +
				"\" root=\"" + ctxt.fRoot + "\" start=" +
				ctxt.fStart + " trigger=\"" + ctxt.fTrigger + "\"");

	}

}
