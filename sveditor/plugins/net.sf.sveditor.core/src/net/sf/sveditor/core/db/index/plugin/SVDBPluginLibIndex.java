package net.sf.sveditor.core.db.index.plugin;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
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
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexCacheData;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.osgi.framework.Bundle;

public class SVDBPluginLibIndex implements ISVDBIndex, ILogLevelListener {
	private LogHandle							fLog;
	private String								fProject;
	private String								fIndexId;
	private String								fRootFile;
	private boolean								fDebugEn;
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
		fRootFile = root;
		
		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");
		logLevelChanged(fLog);
		
		Bundle bundle = Platform.getBundle(plugin_ns);
		fFSProvider = new SVDBPluginFileSystemProvider(bundle, plugin_ns);
		
		fBuildData = new SVDBArgFileIndexBuildData(cache, index_id);
		
		System.out.println("index_id: " + index_id + 
				" plugin_ns: " + plugin_ns + 
				" root: " + root);
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

		monitor.done(); // ?
	}

	// TODO:
	private void ensureIndexUpToDate(IProgressMonitor monitor) {
		
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
		monitor.beginTask("", 1000);
		
		if (sync) {
			ensureIndexUpToDate(new SubProgressMonitor(monitor, 500));
		}

		// Ensure only a single operation runs at a time
		synchronized (fBuildData) {
			try {
				fInIndexOp++;
				op.index_operation(new SubProgressMonitor(monitor, 500), this);
			} finally {
				fInIndexOp--;
			}
		}
		monitor.done();		
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void execIndexChangePlan(IProgressMonitor monitor,
			ISVDBIndexChangePlan plan) {
		// TODO Auto-generated method stub

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
//		if (fIndexBuilder != null) {
//			SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
//			fIndexBuilder.build(plan);
//		} else {
//			// ??
//		}		
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
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isLoaded() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFileListLoaded() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public SVDBIndexConfig getConfig() {
		return null;
	}

}
