package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;

public class SVCoreTestCaseBase extends TestCase {
	
	protected File						fTmpDir;
	protected LogHandle					fLog;
	protected List<IProject>			fProjectList;
	protected TestIndexCacheFactory		fCacheFactory;
//	protected SVDBFileSystem			fFileSystem;
	

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fProjectList = new ArrayList<IProject>();
		
		fLog = LogFactory.getLogHandle(getName());
		
		fTmpDir = TestUtils.createTempDir();
		
		File cache2 = new File(fTmpDir, "cache2");

		/*
		fFileSystem = new SVDBFileSystem(cache2, SVCorePlugin.getVersion());
		fFileSystem.init();
		 */
		
		fCacheFactory = new TestIndexCacheFactory(new File(fTmpDir, "db"));
//		fCacheFactory.init(fFileSystem);
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
		
		for (IProject p : fProjectList) {
			TestUtils.deleteProject(p);
		}
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
		
		LogFactory.removeLogHandle(fLog);
		
	}

	protected void addProject(IProject p) {
		fProjectList.add(p);
	}
	
}
