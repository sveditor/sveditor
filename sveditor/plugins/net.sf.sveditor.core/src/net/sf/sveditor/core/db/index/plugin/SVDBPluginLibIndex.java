package net.sf.sveditor.core.db.index.plugin;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SubMonitor;
import org.osgi.framework.Bundle;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.index.SVDBFindIncFileUtils;
import net.sf.sveditor.core.db.index.SVDBIncFileInfo;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileBuildDataUtils;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileBuildUtils;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexCacheData;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

public class SVDBPluginLibIndex implements ISVDBIndex, ILogLevelListener {
	private LogHandle							fLog;
	private String								fProject;
	private String								fIndexId;
	private String								fRootFile;
	private boolean								fDebugEn;
	private boolean								fIndexValid;
	private SVDBArgFileIndexBuildData			fBuildData;
	private SVDBPluginFileSystemProvider		fFSProvider;
	private int									fInIndexOp;
	private ISVDBIndexBuilder					fIndexBuilder;
	private boolean								fCacheDataValid;
	
	public SVDBPluginLibIndex(
			String 			project, 
			String			index_id,
			String			plugin_ns,
			String			root,
			ISVDBIndexCache	cache) {
		fProject = project;
		fIndexId = index_id;
		fRootFile = "plugin:/" + plugin_ns + "/" + root;
		
		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");
		logLevelChanged(fLog);
		
		Bundle bundle = Platform.getBundle(plugin_ns);
		fFSProvider = new SVDBPluginFileSystemProvider(bundle, plugin_ns);
		
		fBuildData = new SVDBArgFileIndexBuildData(cache, index_id);
		fBuildData.setFSProvider(fFSProvider);
	}
	
	@Override
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		fIndexBuilder = builder;
		
		fBuildData.setIndexCacheData(
				new SVDBArgFileIndexCacheData(getBaseLocation()));
		fCacheDataValid = fBuildData.getCache().init(
				new NullProgressMonitor(),
				fBuildData.getIndexCacheData(),
				getBaseLocation());

		// Queue a job to rebuild this index
//		fIndexBuilder.build(new SVDBIndexChangePlanRebuild(this));

		monitor.done(); // ?
	}

	// TODO:
	private void ensureIndexUpToDate(IProgressMonitor monitor) {
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Ensure Index State for " + getBaseLocation(), 4);
	
		if (!fIndexValid /*|| !fIndexRefreshed */) {
			ISVDBIndexBuildJob build_job = null;
			
			if (fIndexBuilder != null) {
				// See if there is an active job 
				build_job = fIndexBuilder.findJob(this);
				
				if (build_job == null) {
					build_job = fIndexBuilder.build(
							new SVDBIndexChangePlanRebuild(this));
				}
				build_job.waitComplete();
			} else {
//				System.out.println("[ERROR] no builder and invalid");
			}
		}

		subMonitor.done();		
	}

	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = (handle.getDebugLevel() > 0);
	}

	@Override
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		return SVDBArgFileBuildDataUtils.findGlobalScopeDecl(
				fBuildData, monitor, name, matcher);
	}

	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		return fBuildData.getFileList(FILE_ATTR_SRC_FILE);
	}
	
	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		return fBuildData.getFileList(flags);
	}

	@Override
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		synchronized (fBuildData) {
			return SVDBArgFileBuildDataUtils.findFile(fBuildData, monitor, path);
		}		
	}
	
	@Override
	public SVDBFile findFile(String path) {
		return findFile(new NullProgressMonitor(), path);
	}

	@Override
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		SVDBFileTree ft = SVDBArgFileBuildDataUtils.findTargetFileTree(
				fBuildData, path);
		
		return (ft != null)?ft.fSVDBFile:null;
	}
	
	@Override
	public SVDBFile findPreProcFile(String path) {
		return findPreProcFile(new NullProgressMonitor(), path);
	}

	@Override
	public List<SVDBDeclCacheItem> findPackageDecl(
			IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		return SVDBArgFileBuildDataUtils.findPackageDecl(
				fBuildData, monitor, pkg_item);		
	}

	@Override
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		SVDBFile file = null;
		
		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = SVDBArgFileBuildDataUtils.findTargetFileTree(
					fBuildData, item.getFilename());
			if (ft != null) {
				file = ft.getSVDBFile();
			}
		} else {
			/*
			try {
				throw new Exception("getDeclFile");
			} catch (Exception e) {
				e.printStackTrace();
			}
			 */
			file = findFile(item.getFilename());
		}

		return file;		
	}

	@Override
	public SVDBFile getDeclFilePP(IProgressMonitor monitor,
			SVDBDeclCacheItem item) {
		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findFileTree(item.getFilename(), false);
			if (ft != null) {
				file = ft.getSVDBFile();
			}
		} else {
			file = findFile(item.getFilename());
		}

		return file;
	}

	@Override
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		return SVDBFindIncFileUtils.findIncludeFiles(
				this,
				fFSProvider,
				fBuildData.getIncludePathList(),
				root, flags);		
	}

	@Override
	public void execOp(IProgressMonitor monitor, ISVDBIndexOperation op,
			boolean sync) {
		SubMonitor subMonitor = SubMonitor.convert(monitor, "", 1000);
		
		if (sync) {
			ensureIndexUpToDate(subMonitor.newChild(500));
		}

		// Ensure only a single operation runs at a time
		synchronized (fBuildData) {
			try {
				fInIndexOp++;
				op.index_operation(subMonitor.newChild(500), this);
			} finally {
				fInIndexOp--;
			}
		}
		subMonitor.done();		
	}

	@Override
	public List<SVDBFilePath> getFilePath(String path) {
		// Stubbed out
		return new ArrayList<SVDBFilePath>();
	}

	@Override
	public void findReferences(IProgressMonitor monitor,
			ISVDBRefSearchSpec ref_spec, ISVDBRefVisitor ref_matcher) {
		// TODO Auto-generated method stub

	}

	@Override
	public ISVDBIndexChangePlan createIndexChangePlan(
			List<SVDBIndexResourceChangeEvent> changes) {
		return new SVDBIndexChangePlanRebuild(this);
	}

	@Override
	public void execIndexChangePlan(
			IProgressMonitor 		monitor,
			ISVDBIndexChangePlan 	plan) {
		ISVDBIndexCacheMgr c_mgr = fBuildData.getCacheMgr();
		ISVDBIndexCache new_cache = 
				c_mgr.createIndexCache(getProject(), getBaseLocation());
		SVDBArgFileIndexBuildData build_data = new SVDBArgFileIndexBuildData(
				new_cache, getBaseLocation());
		
		// Copy in relevant information
		build_data.setFSProvider(fFSProvider);
	
		build_data.addIncludePath(SVFileUtils.getPathParent(fRootFile));
		
		SVDBArgFileBuildUtils.parseFile(
				fRootFile, build_data, this, 
				new HashMap<String, SVDBMacroDef>());		
		
		if (!monitor.isCanceled()) {
			synchronized (fBuildData) {
				fBuildData.apply(build_data);
			}
			
			// Notify clients that the index has new data
//			synchronized (fIndexChangeListeners) {
//				for (int i=0; i<fIndexChangeListeners.size(); i++) {
//					ISVDBIndexChangeListener l = fIndexChangeListeners.get(i);
//					if (l == null) {
//						fIndexChangeListeners.remove(i);
//						i--;
//					} else {
//						l.index_rebuilt();
//					}
//				}
//			}
			
			fIndexValid = true;
		} else {
			build_data.dispose();
		}			
	}

	@Override
	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor,
			InputStream in, String path, List<SVDBMarker> markers) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVStringPreProcessor createPreProc(String path, InputStream in,
			int limit_lineno) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFSProvider;
	}

	@Override
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		throw new RuntimeException("Cannot set FSProvider for PluginLibrary");
	}


	@Override
	public void dispose() {
		synchronized (fBuildData) {
			if (fBuildData.getCache() != null) {
				fBuildData.getCache().sync();
			}
		}		
	}

	@Override
	public String getBaseLocation() {
		return fIndexId;
	}

	@Override
	public String getProject() {
		return fProject;
	}

	@Override
	public void setGlobalDefine(String key, String val) {
		// Ignore
	}

	@Override
	public void clearGlobalDefines() {
		// Ignore
	}

	@Override
	public String getTypeID() {
		return SVDBPluginLibIndexFactory.TYPE;
	}

	@Override
	public List<SVDBMarker> getMarkers(String path) {
		return SVDBArgFileBuildDataUtils.getMarkers(
				fBuildData, new NullProgressMonitor(), path);
	}


	@Override
	public SVDBFileTree findFileTree(String path, boolean is_argfile) {
		SVDBFileTree ft = null;
		synchronized (fBuildData) {
			ft = fBuildData.getCache().getFileTree(
					new NullProgressMonitor(), path, is_argfile);
		}

		return ft;		
	}


	@Override
	public boolean doesIndexManagePath(String path) {
		path = SVFileUtils.resolvePath(path, getBaseLocation(), 
				fFSProvider, false);
	
		return fBuildData.containsFile(path, 
				FILE_ATTR_SRC_FILE+FILE_ATTR_ARG_FILE);		
	}

	@Override
	public void rebuildIndex(IProgressMonitor monitor) {
		// TODO:
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
			fIndexBuilder.build(plan);
		} else {
			// ??
		}		
	}

	@Override
	public void addChangeListener(ISVDBIndexChangeListener l) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeChangeListener(ISVDBIndexChangeListener l) {
		// TODO Auto-generated method stub

	}

	@Override
	public ISVDBIndexCache getCache() {
		return fBuildData.getCache();
	}

	@Override
	public void loadIndex(IProgressMonitor monitor) {
		ensureIndexUpToDate(monitor);
	}

	@Override
	public boolean isLoaded() {
		return fIndexValid;
	}

	@Override
	public boolean isFileListLoaded() {
		return fIndexValid;
	}

	@Override
	public SVDBIndexConfig getConfig() {
		return null;
	}

}
