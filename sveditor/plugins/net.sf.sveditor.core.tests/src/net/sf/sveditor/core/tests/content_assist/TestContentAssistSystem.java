package net.sf.sveditor.core.tests.content_assist;

import java.io.File;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;

public class TestContentAssistSystem extends TestCase {
	private File				fTmpDir;
	private IProject			fProject;
	private BundleUtils			fUtils;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
		fUtils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
	}

	@Override
	protected void tearDown() throws Exception {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
		super.tearDown();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		if (fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}
	
	public void testGlobalFieldRef() {
		String testname = "testGlobalFieldRef";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(true);
		
		String doc = 
			"class c1;\n" +
			"	function void foo;\n" +
			"		field_c<<MARK>>\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		
		
		fProject = TestUtils.createProject("project");
		
		fUtils.copyBundleDirToWS("/data/content_assist/global_field_ref/", fProject);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/global_field_ref/global_field_ref.f",
				SVDBArgFileIndexFactory.TYPE, null);

		ContentAssistTests.runTest(testname, doc, index, 
				"field_cls");
		
		LogFactory.removeLogHandle(log);		
	}

}
