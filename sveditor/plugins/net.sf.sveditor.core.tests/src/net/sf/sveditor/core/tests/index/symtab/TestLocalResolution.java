package net.sf.sveditor.core.tests.index.symtab;

import java.io.File;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.symtab.SVSymbolTableBuilder;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestLocalResolution extends SVCoreTestCaseBase {
	
	public void testSimpleResolution() {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc = 
				"package foo;\n" +
				"	int		field, field2, field3;\n" +
				"	function void set_field(int v);\n" +
				"		field = v;\n" +
				"	endfunction\n" +
				"endpackage\n"
				;
		String argfile = 
				"./foo.sv\n"
				;
		
		TestUtils.copy(doc, 
				new File(fTmpDir, "foo.sv")
				);
		TestUtils.copy(argfile,
				new File(fTmpDir, "sve.f")
				);
	
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				getName(),
				new File(fTmpDir, "sve.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE,
				null);
		index.execIndexChangePlan(
				new NullProgressMonitor(),
				new SVDBIndexChangePlanRebuild(index));
		
		SVSymbolTableBuilder builder = new SVSymbolTableBuilder(index);
		builder.build();
	}

}
