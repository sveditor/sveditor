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
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.NullProgressMonitor;

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
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		if (root.getProjects() != null) {
			boolean pass = true;
			
			if (root.getProjects().length > 0 && 
					!root.getProjects()[0].getName().equals("RemoteSystemsTempFiles")) {
				pass = false;
			}
			
			if (!pass) {
				for (IProject p : root.getProjects()) {
					if (p.getName().equals("RemoteSystemsTempFiles")) {
						continue;
					}
					System.out.println("Test: " + getName() + " Project: " + p.getName() + " still exists");
					p.delete(true, new NullProgressMonitor());
					if (p.exists()) {
						System.out.println("Test: " + getName() + " Error: failed to delete project " + p.getName());
					}
				}
			}
			assertTrue("Workspace contains " + root.getProjects().length + " projects", pass);
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
			
//			fCacheFactory.dispose();
			
			if (SVCorePlugin.getDefault().getProjMgr() != null) {
				SVCorePlugin.getDefault().getProjMgr().dispose();
			}
			
			for (IProject p : fProjectList) {
				TestUtils.deleteProject(getName(), p);
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
