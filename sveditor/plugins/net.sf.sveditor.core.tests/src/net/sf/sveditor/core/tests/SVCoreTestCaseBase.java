package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.utils.TestUtils;

import junit.framework.TestCase;

public class SVCoreTestCaseBase extends TestCase {
	
	protected File						fTmpDir;
	protected LogHandle					fLog;
	protected List<IProject>			fProjectList;
	protected TestIndexCacheFactory		fCacheFactory;
	

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fProjectList = new ArrayList<IProject>();
		
		fLog = LogFactory.getLogHandle(getName());
		
		fTmpDir = TestUtils.createTempDir();
		
		fCacheFactory = new TestIndexCacheFactory(
				new File(fTmpDir, "db"));
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
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
