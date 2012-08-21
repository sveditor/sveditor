package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefMatcher;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFileOverrideIndex implements ISVDBIndex {
	private SVDBFile				fFile;
	private SVDBFile				fFilePP;
	private ISVDBIndex				fIndex;
	private ISVDBIndexIterator		fItemIterator;
	private List<SVDBMarker>		fMarkers;
	
	public SVDBFileOverrideIndex(
			SVDBFile			file,
			SVDBFile			file_pp,
			ISVDBIndex 			index, 
			ISVDBIndexIterator 	item_it,
			List<SVDBMarker>	markers) {
		fFile = file;
		fFilePP = file_pp;
		fIndex = index;
		fItemIterator = item_it;
		fMarkers = markers;
	}
	
	public void setFile(SVDBFile file) {
		fFile = file;
	}
	
	public void setFilePP(SVDBFile file) {
		fFilePP = file;
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		return fIndex.getItemIterator(monitor);
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		return fItemIterator.findGlobalScopeDecl(monitor, name, matcher);
	}

	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		return fItemIterator.findPackageDecl(monitor, pkg_item);
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		return fItemIterator.getDeclFile(monitor, item);
	}

	public List<SVDBRefCacheItem> findReferences(IProgressMonitor monitor,
			String name, ISVDBRefMatcher matcher) {
		return fItemIterator.findReferences(monitor, name, matcher);
	}

	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		return fIndex.findIncludedFile(leaf);
	}

	public void init(IProgressMonitor monitor) {
		fIndex.init(monitor);
	}

	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor,
			InputStream in, String path, List<SVDBMarker> markers) {
		return fIndex.parse(monitor, in, path, markers);
	}

	public void setEnableAutoRebuild(boolean en) {
		fIndex.setEnableAutoRebuild(en);
	}

	public boolean isDirty() {
		return fIndex.isDirty();
	}

	public void dispose() {
		fIndex.dispose();
	}

	public String getBaseLocation() {
		return fIndex.getBaseLocation();
	}

	public String getProject() {
		return fIndex.getProject();
	}

	public void setGlobalDefine(String key, String val) {
		fIndex.setGlobalDefine(key, val);
	}

	public void clearGlobalDefines() {
		fIndex.clearGlobalDefines();
	}

	public String getTypeID() {
		return fIndex.getTypeID();
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider inc_provider) {
		fIndex.setIncludeFileProvider(inc_provider);
	}

	public Set<String> getFileList(IProgressMonitor monitor) {
		return fIndex.getFileList(monitor);	
	}

	public List<SVDBMarker> getMarkers(String path) {
		if (fFile.getFilePath().equals(path)) {
			return fMarkers;
		} else {
			return fIndex.getMarkers(path);
		}
	}

	public SVDBFile findFile(String path) {
		if (fFile.getFilePath().equals(path)) {
			return fFile;
		} else {
			return fIndex.findFile(path);
		}
	}

	public SVDBFile findPreProcFile(String path) {
		if (fFile.getFilePath().equals(path)) {
			return fFilePP;
		} else {
			return fIndex.findPreProcFile(path);
		}
	}

	public void rebuildIndex(IProgressMonitor monitor) {
		fIndex.rebuildIndex(monitor);
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {
		fIndex.addChangeListener(l);
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		fIndex.removeChangeListener(l);
	}

	public ISVDBIndexCache getCache() {
		return fIndex.getCache();
	}

	public void loadIndex(IProgressMonitor monitor) {
		fIndex.loadIndex(monitor);
	}

	public SVDBIndexConfig getConfig() {
		return fIndex.getConfig();
	}

}
