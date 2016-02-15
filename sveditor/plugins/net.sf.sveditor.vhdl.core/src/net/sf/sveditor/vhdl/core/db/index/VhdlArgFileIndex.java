package net.sf.sveditor.vhdl.core.db.index;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

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
import net.sf.sveditor.core.db.index.SVDBIncFileInfo;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

import org.eclipse.core.runtime.IProgressMonitor;

public class VhdlArgFileIndex implements ISVDBIndex {
	private String								fProject;
	private String								fBaseLocation;
	private String								fResolvedBaseLocation;
	private ISVDBFileSystemProvider				fFSProvider;
	private ISVDBIndexCache						fCache;
	private SVDBIndexConfig						fConfig;
	private List<ISVDBIndexChangeListener>		fChangeListeners;
	
	protected VhdlArgFileIndex() {
		fChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
	}
	
	public VhdlArgFileIndex(
			String						project,
			String						base_location,
			ISVDBFileSystemProvider		fs_provider,
			ISVDBIndexCache				cache,
			SVDBIndexConfig				config) {
		this();
		fProject = project;
		fBaseLocation = base_location;
		fFSProvider = fs_provider;
		fCache = cache;
		fConfig = config;
	}

	@Override
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor 		monitor, 
			String 					name, 
			ISVDBFindNameMatcher 	matcher) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile findFile(IProgressMonitor monitor, String filename) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String filename) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBDeclCacheItem> findPackageDecl(
			IProgressMonitor 		monitor,
			SVDBDeclCacheItem 		pkg_item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile getDeclFilePP(IProgressMonitor monitor,
			SVDBDeclCacheItem item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void findReferences(IProgressMonitor monitor,
			ISVDBRefSearchSpec ref_spec, ISVDBRefVisitor ref_matcher) {
		// TODO Auto-generated method stub
	}

	@Override
	public void execOp(
			IProgressMonitor 		monitor, 
			ISVDBIndexOperation 	op,
			boolean 				sync) {
		// TODO Auto-generated method stub

	}

	@Override
	public List<SVDBFilePath> getFilePath(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVDBIndexChangePlan createIndexChangePlan(
			List<SVDBIndexResourceChangeEvent> changes) {
		// TODO Auto-generated method stub
		return new SVDBIndexChangePlanRebuild(this);
	}

	@Override
	public void execIndexChangePlan(
			IProgressMonitor 		monitor,
			ISVDBIndexChangePlan 	plan) {
		switch (plan.getType()) {
			default:
			case RebuildIndex:
				rebuild_index(monitor);
				break;
				
		}
	}
	
	private void rebuild_index(IProgressMonitor monitor) {
		
	}

	@Override
	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor,
			InputStream in, String path, List<SVDBMarker> markers) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public ISVStringPreProcessor createPreProc(
			String path, 
			InputStream in,
			int limit_lineno) {
		return null;
	}

	@Override
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFSProvider;
	}

	@Override
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFSProvider = fs_provider;
	}

	@Override
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		// TODO Auto-generated method stub

	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public String getBaseLocation() {
		return fBaseLocation;
	}

	@Override
	public String getProject() {
		return fProject;
	}


	@Override
	public String getTypeID() {
		return VhdlArgFileIndexFactory.TYPE;
	}


	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBMarker> getMarkers(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile findFile(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFileTree findFileTree(String path, boolean is_argfile) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile findPreProcFile(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean doesIndexManagePath(String path) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void rebuildIndex(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

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
		return fCache;
	}

	@Override
	public void loadIndex(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

	}

	@Override
	public SVDBIndexConfig getConfig() {
		return fConfig;
	}

	// Back-compat methods
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
	public void setGlobalDefine(String key, String val) { }

	@Override
	public void clearGlobalDefines() { }
}
