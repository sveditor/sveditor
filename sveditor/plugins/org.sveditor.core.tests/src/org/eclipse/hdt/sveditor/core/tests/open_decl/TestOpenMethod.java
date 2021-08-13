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
package org.eclipse.hdt.sveditor.core.tests.open_decl;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBOverrideFilesystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprContext;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclResult;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclUtils;
import org.eclipse.hdt.sveditor.core.scanutils.IBIDITextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.TestStringUtils;
public class TestOpenMethod extends SVCoreTestCaseBase { 
	
	public void testExternFieldBehaveBlock() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"package foobar_pkg;\n" +
			"\n" +
			"	class bar;\n" +
			"		int int_value;\n" +
			"	endclass\n" +
			"\n" +
			"	class foo;\n" +
			"		bar    bar_inst;\n" +
			"		extern task do_something();\n" +
			"	endclass : foo\n" +
			"\n" +
			"	task foo::do_something();\n" +
			"		//Open declaration on either of these is ok\n" +
			"		bar_inst.int_value++;\n" +
			"\n" +
			"		forever begin\n" +
			"			//Open declaration on either of these fails\n" +
			"			bar_inst.int_value++;\n" +
			"			#10ns;\n" +
			"		end\n" +
			"	endtask\n" +
			"endpackage\n"
			;
		SVDBOverrideFilesystemProvider fs = new SVDBOverrideFilesystemProvider();
		fs.addFile("/foobar_pkg.sv", doc);
		fs.addFile("/sve.f", "/foobar_pkg.sv\n");
	
		SVDBArgFileIndex index = createArgFileIndex("GLOBAL", "/sve.f", fs);
	
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
	
		SVDBFile file = index.findFile("/foobar_pkg.sv");
		assertNotNull(file);
		
		int idx = doc.indexOf("forever begin");
		assertTrue(idx != -1);
	
		idx = doc.indexOf("bar_inst.", idx);
		assertTrue(idx != -1);
		
		idx += "bar_inst.int".length();
		
		int line = TestStringUtils.lineOfIndex(doc, idx);
		
		IBIDITextScanner scanner = new StringBIDITextScanner(doc);
		scanner.seek(idx);
		
		Tuple<SVExprContext, ISVDBScopeItem> ctxt = OpenDeclUtils.getContextScope(
				file, line, scanner);
		
		List<OpenDeclResult> results = OpenDeclUtils.openDecl(
				ctxt.first(), ctxt.second(), index);
		
		assertEquals(1, results.size());
	}

	public void testSuperFieldBehaveBlock() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"package foobar_pkg;\n" +
			"\n" +
			"	class bar;\n" +
			"		int int_value;\n" +
			"	endclass\n" +
			"\n" +
			"	class baz extends bar;\n" +
			"		int int_value1;\n" +
			"	endclass\n" +
			"\n" +
			"	class foo;\n" +
			"		baz    bar_inst;\n" +
			"		extern task do_something();\n" +
			"	endclass : foo\n" +
			"\n" +
			"	task foo::do_something();\n" +
			"		//Open declaration on either of these is ok\n" +
			"		bar_inst.int_value++;\n" +
			"\n" +
			"		forever begin\n" +
			"			//Open declaration on either of these fails\n" +
			"			bar_inst.int_value++;\n" +
			"			#10ns;\n" +
			"		end\n" +
			"	endtask\n" +
			"endpackage\n"
			;
		SVDBOverrideFilesystemProvider fs = new SVDBOverrideFilesystemProvider();
		fs.addFile("/foobar_pkg.sv", doc);
		fs.addFile("/sve.f", "/foobar_pkg.sv\n");
	
		SVDBArgFileIndex index = createArgFileIndex("GLOBAL", "/sve.f", fs);
	
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
	
		SVDBFile file = index.findFile("/foobar_pkg.sv");
		assertNotNull(file);
		
		int idx = doc.indexOf("forever begin");
		assertTrue(idx != -1);
	
		idx = doc.indexOf("bar_inst.", idx);
		assertTrue(idx != -1);
		
		idx += "bar_inst.int".length();
		
		int line = TestStringUtils.lineOfIndex(doc, idx);
		
		IBIDITextScanner scanner = new StringBIDITextScanner(doc);
		scanner.seek(idx);
		
		Tuple<SVExprContext, ISVDBScopeItem> ctxt = OpenDeclUtils.getContextScope(
				file, line, scanner);
		
		List<OpenDeclResult> results = OpenDeclUtils.openDecl(
				ctxt.first(), ctxt.second(), index);
		
		assertEquals(1, results.size());
	}

}
