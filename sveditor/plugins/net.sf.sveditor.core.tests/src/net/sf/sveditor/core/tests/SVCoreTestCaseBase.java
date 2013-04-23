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
	protected File						fDbDir;
	protected LogHandle					fLog;
	protected List<IProject>			fProjectList;
	protected TestIndexCacheFactory		fCacheFactory;
//	protected SVDBFileSystem			fFileSystem;
	protected SVDBIndexRegistry			fIndexRgy;
	

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
	
		fDbDir = new File(fTmpDir, "db");
		fCacheFactory = new TestIndexCacheFactory(fDbDir);
//		fCacheFactory.init(fFileSystem);
		
		fIndexRgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		fIndexRgy.init(fCacheFactory);
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
		
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
	
	protected void reinitializeIndexRegistry() {
		// Close down registry
		// Note: this also disposes the cache factory
		fIndexRgy.close();
	
		// Re-create the cache factory
		fCacheFactory = new TestIndexCacheFactory(fDbDir);
		
		fIndexRgy.init(fCacheFactory);
		
	}
	
}
