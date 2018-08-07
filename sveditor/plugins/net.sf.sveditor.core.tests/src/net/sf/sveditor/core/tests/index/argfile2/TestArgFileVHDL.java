package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.search.SVDBFindAllMatcher;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestArgFileVHDL extends SVCoreTestCaseBase {
	
	public void testSmoke() {
		
		SVFileUtils.copy(
				"foo",
				new File(fTmpDir, "foo.vhd"));
		
		SVFileUtils.copy(
				"foo.vhd",
				new File(fTmpDir, "sve.f"));
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), 
				getName(),
				new File(fTmpDir, "sve.f").getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, 
				null);
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		
		index.findGlobalScopeDecl(new NullProgressMonitor(), 
				"", new SVDBFindAllMatcher());
		
	}

}
