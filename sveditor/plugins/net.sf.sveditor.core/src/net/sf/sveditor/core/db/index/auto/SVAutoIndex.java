package net.sf.sveditor.core.db.index.auto;

import java.io.InputStream;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.builder.ISVBuilderOutput;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
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
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

public class SVAutoIndex implements 
	ISVDBIndex, ISVDBIndexInt{
	
	private ISVDBFileSystemProvider		fFileSystemProvider;
	private String						fBaseLocation;

	public SVAutoIndex(
			String 						project, 
			String 						base_location,
			ISVDBFileSystemProvider 	fs_provider, 
			ISVDBIndexCache 			cache,
			SVDBIndexConfig 			config) {
		fBaseLocation = base_location;
		fFileSystemProvider = fs_provider;
	}

	@Override
	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		// TODO: always rebuild for now
		return new SVDBIndexChangePlanRebuild(this);
	}

	@Override
	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
		switch (plan.getType()) {
		default: // TODO: always rebuild now
		case RebuildIndex:
			break;
		}
		// TODO Auto-generated method stub
		
	}

	@Override
	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor, InputStream in, String path,
			List<SVDBMarker> markers) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVStringPreProcessor createPreProc(String path, InputStream in, int limit_lineno) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(IProgressMonitor monitor, String name,
			ISVDBFindNameMatcher matcher) {
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
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor, SVDBDeclCacheItem pkg_item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void execOp(IProgressMonitor monitor, ISVDBIndexOperation op, boolean sync) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public List<SVDBFilePath> getFilePath(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void findReferences(IProgressMonitor monitor, ISVDBRefSearchSpec ref_spec, ISVDBRefVisitor ref_matcher) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public ISVPreProcessor createPreProcScanner(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getFileFromId(int fileid) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}

	@Override
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setBuilderOutput(ISVBuilderOutput out) {
		// TODO Auto-generated method stub
		
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setGlobalDefine(String key, String val) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void clearGlobalDefines() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public String getTypeID() {
		// TODO Auto-generated method stub
		return null;
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
		// TODO Auto-generated method stub
		return null;
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
		// TODO Auto-generated method stub
		return null;
	}
	
	
}
