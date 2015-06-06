package net.sf.sveditor.core.tests.open_decl;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBOverrideFilesystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.expr_utils.SVExprContext;
import net.sf.sveditor.core.open_decl.OpenDeclResult;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.TestStringUtils;
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
	
		SVDBArgFileIndex2 index = createArgFileIndex("GLOBAL", "/sve.f", fs);
	
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
	
		SVDBArgFileIndex2 index = createArgFileIndex("GLOBAL", "/sve.f", fs);
	
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
