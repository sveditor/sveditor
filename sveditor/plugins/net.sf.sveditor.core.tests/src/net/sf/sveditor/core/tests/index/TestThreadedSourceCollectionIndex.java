package net.sf.sveditor.core.tests.index;

import java.io.File;

import junit.framework.TestCase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;

public class TestThreadedSourceCollectionIndex extends TestCase {
	private File			fTmpDir;
	private IProject		fProject;

	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
			fProject = null;
		}
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	}
	
}
