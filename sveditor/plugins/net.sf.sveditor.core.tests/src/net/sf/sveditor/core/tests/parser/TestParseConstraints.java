/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.parser;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVLanguageLevel;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParseConstraints extends SVCoreTestCaseBase {
	
	public void testParseConstraintFunction() {
		String doc = 
				"class bob;\n" +
				"	constraint c_unique_sources { unique {sources, other_sources}; };\n" +
				"	constraint some_constraint {\n" +
				"		if (1) {\n" +
//				"			some_variable  == some_function(.arg1(value1)); // Commenting this in or  out affects the error on the next line\n" +
				"			some_variable  == some_function(.arg1(value1), .arg2(value2));\n" +
				"		}\n" +
				"	}\n" +
				"endclass\n"
				;
	
		runTest(doc, new String[] {"bob", "c_unique_sources", "some_constraint"});
	}
	
	public void testSingleStmtImplication() {
		String doc = 
			"class c;\n" +
			"	constraint c_always_running_base  {\n" +
			"		foreach(fixed_base[i]) (i != 0 -> fixed_base[i] == 0);\n" +
			"		fixed_base[0] == 1;\n" +
			"	}\n" +
			"endclass\n";
		SVCorePlugin.getDefault().enableDebug(false);
		runTest(doc, new String[] {"c", "c_always_running_base"});
	}
	
	public void testForeach() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class top;\n" +
			"	constraint some_const {\n" +
			"		if (thing.opcode inside {thingy::SFR_WR, \n" +
			"			thingy::SFR_RD,\n" +
			"			thingy::SFR_BIT_SET,\n" +
			"			thingy::SFR_BIT_CLR,\n" +
			"			thingy::SFR_BIT_INV\n" +
			"			}) {\n" +
			"				foreach (transaction[i]) {\n" +
			"					if (i <length) {\n" +
			"						transaction[i].byte_en == get_byte_en(.tran_num (i), \n" +
			"							.be       (data.byte_en), \n" +
			"							.cpu      (cfg.cpu));\n" +
			"					}\n" +
			"				}\n" +
			"			}\n" +
			"	}\n" +
			"endclass\n"
			;
		
		runTest(doc, new String[] {"top", "some_const"});
	}
	public void testIfInside() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
				"class top;\n" +
				"	int a, b;\n" +
				"	constraint c_con {\n" +
				"		if(a == b) {a inside {1,3}};\n" +
				"			else {a inside {0,2}};\n" +
				"		}\n" +
				"endclass\n"
				;
		
		runTest(doc, new String[] {"top", "c_con"});
	}

	private void runTest(
			String			doc,
			String			exp_items[]) {
		LogHandle log = LogFactory.getLogHandle(getName());
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		Tuple<SVDBFile, SVDBFile> result = SVDBTestUtils.parse(
				log, SVLanguageLevel.SystemVerilog, null, 
				new StringInputStream(doc), getName(), markers);
		
		SVDBFile file = result.second();
		
		assertEquals("Unexpected errors", 0, markers.size());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		LogFactory.removeLogHandle(log);
	}
	
}
