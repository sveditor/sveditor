package net.sf.sveditor.core.tests.index;

import java.io.File;

import net.sf.sveditor.core.tests.utils.TestUtils;

import junit.framework.TestCase;

public class TestFileSystemSourceCollectionIndex extends TestCase {
	private File			fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}
	
//	public void testDefaultSourceCollection

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
		}
	}
	
	

}
