package net.sf.sveditor.core.tests.docs;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.search.SVDBFindDocComment;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestFindDocComments extends TestCase {
	
	private File				fTmpDir;
	private IProject			fProject;
	
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		File db = new File(fTmpDir, "db");
		
		assertTrue(db.mkdirs());
		
		rgy.init(new TestIndexCacheFactory(db));
	}

	@Override
	protected void tearDown() throws Exception {
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}

	public void testFindUvmReportObject() {
		String testname = "testFindUvmReportObject";
		LogHandle log = LogFactory.getLogHandle(testname);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		File uvm = new File(fTmpDir, "uvm");

		File uvm_report_object_svh = new File(uvm, "src/base/uvm_report_object.svh");
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		Tuple<SVDBFile, SVDBFile> file = SVDBTestUtils.parse(log, uvm_report_object_svh, markers); 
	
		assertNotNull(file);
	
		FileIndexIterator index_it = new FileIndexIterator(file);
		
		SVDBFindNamedClass finder = new SVDBFindNamedClass(index_it);
		List<SVDBClassDecl> result = finder.find("uvm_report_object");
		
		assertTrue(result.size() == 1);
		
		SVDBClassDecl uvm_report_object = result.get(0);
		
		SVDBFindDocComment comment_finder = new SVDBFindDocComment(index_it);
		
		SVDBDocComment comment = comment_finder.find(new NullProgressMonitor(), uvm_report_object);
		
		assertNotNull(comment);
	}

}
