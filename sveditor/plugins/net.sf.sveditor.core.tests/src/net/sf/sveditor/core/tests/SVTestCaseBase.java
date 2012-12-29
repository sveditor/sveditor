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

public class SVTestCaseBase extends TestCase {
	protected LogHandle					fLog;
	protected List<IProject>			fProjects;
	protected File						fTmpDir;

	
	@Override
	protected void setUp() throws Exception {
		fLog = LogFactory.getLogHandle(getName());
		fTmpDir = TestUtils.createTempDir();
		fProjects = new ArrayList<IProject>();
		
		SVCorePlugin.setTestMode();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		File db = new File(fTmpDir, "db");
		assertTrue(db.mkdirs());
		
		rgy.init(new TestIndexCacheFactory(db));
		SVCorePlugin.getDefault().getProjMgr().init();
		
		CoreReleaseTests.clearErrors();
	}
	
	@Override
	protected void tearDown() throws Exception {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
		SVCorePlugin.getJobMgr().dispose();
		
		for (IProject p : fProjects) {
			TestUtils.deleteProject(p);
		}

		for (int i=0; i<4; i++) {
			if (i+1 == 4) {
				TestUtils.delete(fTmpDir);
			} else if (TestUtils.safe_delete(fTmpDir)) {
				break;
			} else {
				try {
					Thread.sleep(500);
				} catch (InterruptedException e) {}
			}
		}
		
		assertFalse(fTmpDir.exists());
		
		StringBuilder errors = new StringBuilder();
		for (Exception e : CoreReleaseTests.getErrors()) {
			errors.append(e.getMessage() + " ");
		}
		
		assertEquals(errors.toString(), 0, CoreReleaseTests.getErrors().size());
		
		LogFactory.removeLogHandle(fLog);
	}

	protected void addProject(IProject p) {
		fProjects.add(p);
	}
	

}
