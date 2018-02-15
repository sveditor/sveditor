package net.sf.sveditor.core.tests.docs;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.search.SVDBFindDocComment;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestFindDocComments extends SVCoreTestCaseBase {
	
	public void testFindUvmReportObject() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(true);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		File uvm = new File(fTmpDir, "uvm");
		
		TestUtils.copy(
				"+incdir+./uvm/src\n" +
				"+define+QUESTA\n" +
				"./uvm/src/uvm_pkg.sv\n",
				new File(fTmpDir, "uvm.f"));

		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"global", 
				new File(fTmpDir, "uvm.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE,
				null);
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		
		SVDBFindNamedClass finder = new SVDBFindNamedClass(index);
		List<SVDBClassDecl> result = finder.findItem("uvm_report_object");
		
		assertEquals(1, result.size());
		
		SVDBClassDecl uvm_report_object = result.get(0);
		
		SVDBFindDocComment comment_finder = new SVDBFindDocComment(index);
		
		SVDBDocComment comment = comment_finder.find(new NullProgressMonitor(), uvm_report_object);
		
		assertNotNull(comment);
	}

}
