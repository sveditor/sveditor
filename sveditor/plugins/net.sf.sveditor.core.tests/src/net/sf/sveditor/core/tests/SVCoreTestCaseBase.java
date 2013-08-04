package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;

public class SVCoreTestCaseBase extends TestCase implements ILogLevel {
	
	protected File						fTmpDir;
	protected File						fDbDir;
	protected LogHandle					fLog;
	protected List<IProject>			fProjectList;
	protected List<ISVDBIndex>			fStandaloneIndexList;
	protected TestIndexCacheFactory		fCacheFactory;
//	protected SVDBFileSystem			fFileSystem;
	protected SVDBIndexRegistry			fIndexRgy;
	

	@Override
	protected void setUp() throws Exception {
		SVCorePlugin.setTestMode();
		
		if (SVCorePlugin.getDefault() != null) {
			SVCorePlugin.getDefault().getResourceChangeListener().init();
		}
		
		fProjectList = new ArrayList<IProject>();
		fStandaloneIndexList = new ArrayList<ISVDBIndex>();
		
		fLog = LogFactory.getLogHandle(getName());
		
		fTmpDir = TestUtils.createTempDir();
		
		/*
		File cache2 = new File(fTmpDir, "cache2");
		fFileSystem = new SVDBFileSystem(cache2, SVCorePlugin.getVersion());
		fFileSystem.init();
		 */
	
		fDbDir = new File(fTmpDir, "db");
		fCacheFactory = new TestIndexCacheFactory(fDbDir);
//		fCacheFactory.init(fFileSystem);

		if (SVCorePlugin.getDefault() != null) {
			fIndexRgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			fIndexRgy.init(fCacheFactory);
		}
		
		CoreReleaseTests.clearErrors();
	}

	@Override
	protected void tearDown() throws Exception {
		// Stop any active jobs first
		if (SVCorePlugin.getDefault() != null) {
			SVCorePlugin.getDefault().getIndexBuilder().dispose();
		}
		
		if (SVCorePlugin.getDefault() != null) {
			if (SVCorePlugin.getDefault().getResourceChangeListener() != null) {
				SVCorePlugin.getDefault().getResourceChangeListener().dispose();
			}
		
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			rgy.close();
			
			fCacheFactory.dispose();
			
			if (SVCorePlugin.getDefault().getProjMgr() != null) {
				SVCorePlugin.getDefault().getProjMgr().dispose();
			}
			
			for (IProject p : fProjectList) {
				TestUtils.deleteProject(p);
			}
		} else {
			fCacheFactory.dispose();
		}
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	
		LogFactory.removeLogHandle(fLog);
		
		CoreReleaseTests.clearErrors();
	}

	protected void addProject(IProject p) {
		fProjectList.add(p);
	}
	
	protected void addStandaloneIndex(ISVDBIndex index) {
		fStandaloneIndexList.add(index);
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
