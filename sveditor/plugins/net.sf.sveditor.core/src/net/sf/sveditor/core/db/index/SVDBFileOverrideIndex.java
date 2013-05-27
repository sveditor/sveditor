package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.refs.ISVDBRefMatcher;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBFileOverrideIndex 
	implements ISVDBIndex, ISVDBIndexIterator, ILogLevel,
		ISVDBIncludeFileProviderObsolete {
	private SVDBFile				fFile;
	private SVDBFile				fFilePP;
	private SVDBFileTree			fFileTree;
	private ISVDBIndex				fIndex;
	private ISVDBIndexIterator		fSuperIterator;
	private List<SVDBMarker>		fMarkers;
	private LogHandle				fLog;
	
	public SVDBFileOverrideIndex(
			SVDBFile			file,
			SVDBFile			file_pp,
			ISVDBIndex 			index, 
			ISVDBIndexIterator 	item_it,
			List<SVDBMarker>	markers) {
		fFile = file;
		fFilePP = file_pp;
		fIndex = index;
		fSuperIterator = item_it;
		fMarkers = markers;
		fLog = LogFactory.getLogHandle(getClass().getName());
	}
	
	public void setFile(SVDBFile file) {
		fFile = file;
	}
	
	public void setFilePP(SVDBFile file) {
		fFilePP = file;
	}
	
	public ISVDBIndex getBaseIndex() {
		return fIndex;
	}

	public void setIndexBuilder(ISVDBIndexBuilder builder) { }

	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		return new SVDBIndexChangePlan(this, SVDBIndexChangePlanType.Empty);
	}

	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
		// Do nothing
	}
	

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		if (fSuperIterator != null) {
			ISVDBItemIterator super_it = fSuperIterator.getItemIterator(monitor);
			if (super_it instanceof SVDBIndexCollectionItemIterator) {
				SVDBIndexCollectionItemIterator it = (SVDBIndexCollectionItemIterator)super_it;
				it.setOverride(fIndex, fFile);
				return it;
			} else {
				return super_it;
			}
		} else {
			return SVEmptyItemIterator;
		}		
	}
	
	private ISVDBItemIterator SVEmptyItemIterator = new ISVDBItemIterator() {
		public ISVDBItemBase nextItem(SVDBItemType... type_list) { return null; }
		public boolean hasNext(SVDBItemType... type_list) { return false; }
	};	

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		List<SVDBDeclCacheItem> ret = fSuperIterator.findGlobalScopeDecl(monitor, name, matcher);

		// First, remove any results from this file
		for (int i=0; i<ret.size(); i++) {
			/*
			if (ret.get(i) == null) {
				System.out.println("Element " + i + " is null");
			}
			if (ret.get(i).getFile() == null) {
				System.out.println("Element " + i + " has null file");
				continue;
			} else if (ret.get(i).getFile().getFilePath() == null) {
				System.out.println("Element filepath " + i + " has null file");
				continue;
			}
			if (fFile == null) {
				System.out.println("fFile == null");
			}
			if (fFile.getFilePath() == null) {
				System.out.println("getFilePath == null");
			}
			 */
			String filepath = ret.get(i).getFilename();
			String filepath_f = fFile.getFilePath();
			if (filepath != null && filepath.equals(filepath_f)) {
				fLog.debug(LEVEL_MID, "Remove item \"" + ret.get(i).getName() + "\" because from active file");
				ret.remove(i);
				i--;
			}
		}
		
		// Okay, now do a local search from the overriding file
		findDecl(ret, fFile, name, matcher);
		
		return ret;		
	}

	private void findDecl(
			List<SVDBDeclCacheItem> 	result, 
			ISVDBChildParent 			scope,
			String						name,
			ISVDBFindNameMatcher		matcher) {
		for (ISVDBChildItem item : scope.getChildren()) {
			if (item.getType().isElemOf(SVDBItemType.PackageDecl,
					SVDBItemType.Function, SVDBItemType.Task,
					SVDBItemType.ClassDecl, SVDBItemType.ModuleDecl, 
					SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl, 
					SVDBItemType.TypedefStmt, SVDBItemType.MacroDef)) {
				if (item instanceof ISVDBNamedItem) {
					boolean is_ft = item.getType().isElemOf(
							SVDBItemType.MacroDef);
					ISVDBNamedItem ni = (ISVDBNamedItem)item;
					if (matcher.match(ni, name)) {
						fLog.debug(LEVEL_MID, "Add item \"" + ni.getName() + "\" to result");
						result.add(new SVDBDeclCacheItem(this, fFile.getFilePath(), 
								ni.getName(), ni.getType(), is_ft));
					}
				}
				if (item.getType() == SVDBItemType.PackageDecl) {
					findDecl(result, (ISVDBChildParent)item, name, matcher);
				}
			} else if (item.getType() == SVDBItemType.PreProcCond) {
				findDecl(result, (ISVDBChildParent)item, name, matcher);
			}
		}
	}
	
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		return fSuperIterator.findPackageDecl(monitor, pkg_item);
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		if (item.getFilename().equals(fFile.getFilePath())) {
			return fFile;
		} else {
			return fSuperIterator.getDeclFile(monitor, item);
		}
	}
	
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		if (item.getFilename().equals(fFile.getFilePath())) {
			return fFile;
		} else {
			return fSuperIterator.getDeclFilePP(monitor, item);
		}		
	}

	public List<SVDBRefCacheItem> findReferences(IProgressMonitor monitor,
			String name, ISVDBRefMatcher matcher) {
		return fSuperIterator.findReferences(monitor, name, matcher);
	}

	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		if (fIndex instanceof ISVDBIncludeFileProviderObsolete) {
			return ((ISVDBIncludeFileProviderObsolete)fIndex).findIncludedFile(leaf);
		} else {
			return null;
		}
	}
	
	public SVDBSearchResult<String> findIncludedFilePath(String leaf) {
		return fIndex.findIncludedFilePath(leaf);
	}

	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fIndex.getFileSystemProvider();
	}
	
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fIndex.setFileSystemProvider(fs_provider);
	}

	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		fIndex.init(monitor, builder);
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

	public Iterable<String> getFileList(IProgressMonitor monitor) {
		return fSuperIterator.getFileList(monitor);	
	}
	
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		return findFile(path);
	}
	
	public SVDBFileTree findFileTree(String path, boolean is_argfile) {
		// TODO: probably incorrect
		if (fFile.getFilePath().equals(path)) {
			return fFileTree;
		} else {
			return null;
		}
	}

	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		return findPreProcFile(path);
	}
	
	public boolean doesIndexManagePath(String path) {
		return (fFileTree.getFilePath().equals(path));
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
			return fSuperIterator.findFile(new NullProgressMonitor(), path);
		}
	}

	public SVDBFile findPreProcFile(String path) {
		if (fFile.getFilePath().equals(path)) {
			return fFilePP;
		} else {
			return fSuperIterator.findPreProcFile(new NullProgressMonitor(), path);
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
	
	public boolean isLoaded() {
		return fIndex.isLoaded();
	}
	
	public boolean isFileListLoaded() {
		return fIndex.isFileListLoaded();
	}

	public SVDBIndexConfig getConfig() {
		return fIndex.getConfig();
	}

	public void execOp(IProgressMonitor monitor, ISVDBIndexOperation op, boolean sync) {
		fIndex.execOp(monitor, op, sync);
	}
	
}
