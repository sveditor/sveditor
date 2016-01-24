package net.sf.sveditor.core.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
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
		
		IWorkspaceRoot root = null;
		
		try {
			root = ResourcesPlugin.getWorkspace().getRoot();
		} catch (IllegalStateException e) {}
		
		if (root != null && root.getProjects() != null) {
			List<IProject> projects = new ArrayList<IProject>();
			for (IProject p : root.getProjects()) {
				if (!p.getName().equals("RemoteSystemsTempFiles")) {
					projects.add(p);
				}
			}
			boolean pass = (projects.size() == 0);
			
			if (!pass) {
				for (IProject p : projects) {
					System.out.println("Test: " + getName() + " Project: " + p.getName() + " still exists");
					p.delete(true, new NullProgressMonitor());
					if (p.exists()) {
						System.out.println("Test: " + getName() + " Error: failed to delete project " + p.getName());
					}
				}
			}
			assertTrue("Workspace contains " + projects.size() + " projects", pass);
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
		
		// Restore environment
		SVCorePlugin.clearenv();
		
		
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
//			fCacheFactory.dispose();
		}
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
	
		LogFactory.removeLogHandle(fLog);
		
		CoreReleaseTests.clearErrors();
	}
	
	protected IProject createProject(String name, File path) {
		IProject p = TestUtils.createProject(name, path);
		addProject(p);
		return p;
	}
	
	protected SVDBArgFileIndex createArgFileIndex(
			String						project,
			String						base_location,
			ISVDBFileSystemProvider		fs_provider
			) {
		ISVDBIndexCacheMgr cache_mgr = fIndexRgy.getCacheMgr();
		ISVDBIndexCache cache = cache_mgr.findIndexCache(project, base_location);
		if (cache == null) {
			cache = fCacheFactory.createIndexCache(project, base_location);
		}		
		return createArgFileIndex(project, base_location, fs_provider, cache);
	}

	protected SVDBArgFileIndex createArgFileIndex(
			String						project,
			String						base_location,
			ISVDBFileSystemProvider		fs_provider,
			ISVDBIndexCache				cache
			) {
		SVDBArgFileIndex index = new SVDBArgFileIndex(project, base_location, 
				fs_provider, cache, null);
		// TODO: may wish to track and tear down
		return index;
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
