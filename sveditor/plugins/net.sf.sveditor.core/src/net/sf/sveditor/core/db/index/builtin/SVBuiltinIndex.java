package net.sf.sveditor.core.db.index.builtin;

import java.io.InputStream;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.builder.ISVBuilderOutput;
import net.sf.sveditor.core.db.ISVDBVisitor;
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
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

public class SVBuiltinIndex implements ISVDBIndex {

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
		return null;
	}

	@Override
	public SVDBFile findFile(IProgressMonitor monitor, String filename) {
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
	
	public String mapFileIdToPath(int id) {
		// TODO:
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
	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
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
	public ISVDBFileSystemProvider getFileSystemProvider() {
		// TODO Auto-generated method stub
		return null;
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getProject() {
		// TODO Auto-generated method stub
		return null;
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
	public void addChangeListener(ISVDBIndexChangeListener l) { }

	@Override
	public void removeChangeListener(ISVDBIndexChangeListener l) { }

	@Override
	public ISVDBIndexCache getCache() {
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

	@Override
	public void accept(ISVDBVisitor v) {
		// TODO Auto-generated method stub
		
	}

	
}
