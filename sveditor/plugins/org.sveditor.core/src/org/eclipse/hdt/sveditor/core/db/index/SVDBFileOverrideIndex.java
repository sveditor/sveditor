/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.index;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.builder.ISVBuilderOutput;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import org.eclipse.hdt.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.refs.ISVDBRefSearchSpec;
import org.eclipse.hdt.sveditor.core.db.refs.ISVDBRefVisitor;
import org.eclipse.hdt.sveditor.core.db.search.ISVDBFindNameMatcher;
import org.eclipse.hdt.sveditor.core.db.search.SVDBSearchResult;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.preproc.ISVStringPreProcessor;

public class SVDBFileOverrideIndex 
	implements ISVDBIndex, ISVDBIndexIterator, ILogLevel {
	private SVDBFile					fFile;
	private SVDBFile					fFilePP;
	private SVDBFileTree				fFileTree;
	private ISVDBIndex					fIndex;
	private ISVDBIndexIterator			fSuperIterator;
	private ISVDBIncludeFilesFinder		fIncFilesFinder;
	private List<SVDBMarker>			fMarkers;
	private LogHandle					fLog;
	
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
		
		fIncFilesFinder = fIndex;
	}
	
	@Override
	public void setBuilderOutput(ISVBuilderOutput out) { }

	public void setFile(SVDBFile file) {
		fFile = file;
	}
	
	public void setFilePP(SVDBFile file) {
		fFilePP = file;
	}
	
	public ISVDBIndex getBaseIndex() {
		return fIndex;
	}
	
	public void setBaseIndex(ISVDBIndex index) {
		fIndex = index;
	}
	
	public void setIncFilesFinder(ISVDBIncludeFilesFinder inc_p) {
		fIncFilesFinder = inc_p;
	}

	public void setIndexBuilder(ISVDBIndexBuilder builder) { }

	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		return new SVDBIndexChangePlan(this, SVDBIndexChangePlanType.Empty);
	}

	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
		// Do nothing
	}
	

	/*
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
	 */
	
	public List<SVDBFilePath> getFilePath(String path) {
		if (fSuperIterator != null) {
			return fSuperIterator.getFilePath(path);
		} else {
			return new ArrayList<SVDBFilePath>();
		}
	}


	private ISVDBItemIterator SVEmptyItemIterator = new ISVDBItemIterator() {
		public ISVDBItemBase nextItem(SVDBItemType... type_list) { return null; }
		public boolean hasNext(SVDBItemType... type_list) { return false; }
	};	

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		List<SVDBDeclCacheItem> ret;
		if (fSuperIterator != null) {
			ret = fSuperIterator.findGlobalScopeDecl(monitor, name, matcher);
		} else {
			ret = new ArrayList<SVDBDeclCacheItem>();
		}

		// First, remove any results from this file
		for (int i=0; i<ret.size(); i++) {
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
		findDecl(ret, fFilePP, name, matcher);
		
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
		if (fSuperIterator != null) {
			return fSuperIterator.findPackageDecl(monitor, pkg_item);
		} else {
			return new ArrayList<SVDBDeclCacheItem>();
		}
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		if (item.getFilename().equals(fFile.getFilePath())) {
			if (item.isFileTreeItem()) {
				return fFilePP;
			} else {
				return fFile;
			}
		} else if (fSuperIterator != null) {
			return fSuperIterator.getDeclFile(monitor, item);
		} else {
			return null;
		}
	}
	
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		if (item.getFilename().equals(fFile.getFilePath())) {
			return fFilePP;
		} else if (fSuperIterator != null) {
			return fSuperIterator.getDeclFilePP(monitor, item);
		} else {
			return null;
		}
	}

	public void findReferences(
			IProgressMonitor 		monitor,
			ISVDBRefSearchSpec		ref_spec,
			ISVDBRefVisitor			ref_matcher) {
		if (fSuperIterator != null) {
			fSuperIterator.findReferences(
					monitor, ref_spec, ref_matcher);
		}
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
	
	@Override
	public ISVStringPreProcessor createPreProc(
			String 			path, 
			InputStream 	in,
			int 			limit_lineno) {
		if (fIndex != null) {
			// TODO: should add in locally-added macros?
			return fIndex.createPreProc(path, in, limit_lineno);
		}

		return null;
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

	public Iterable<String> getFileList(IProgressMonitor monitor) {
		if (fIndex != null) {
			return fIndex.getFileList(monitor);
		} else {
			List<String> ret = new ArrayList<String>();
			ret.add(fFile.getFilePath());
			return ret;
		}
	}
	
	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		if (fIndex != null) {
			return fIndex.getFileList(monitor, flags);
		} else {
			// TODO: Not exactly right...
			List<String> ret = new ArrayList<String>();
			ret.add(fFile.getFilePath());
			return ret;
		}
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
		} else if (fIndex != null) {
			return fIndex.getMarkers(path);
		} else {
			return new ArrayList<SVDBMarker>();
		}
	}

	public SVDBFile findFile(String path) {
		if (fFile.getFilePath().equals(path)) {
			return fFile;
		} else if (fSuperIterator != null) {
			return fSuperIterator.findFile(new NullProgressMonitor(), path);
		} else {
			return null;
		}
	}

	public SVDBFile findPreProcFile(String path) {
		if (fFile.getFilePath().equals(path)) {
			return fFilePP;
		} else if (fSuperIterator != null) {
			return fSuperIterator.findPreProcFile(new NullProgressMonitor(), path);
		} else {
			return null;
		}
	}

	public void rebuildIndex(IProgressMonitor monitor) {
		if (fIndex != null) {
			fIndex.rebuildIndex(monitor);
		}
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {
		if (fIndex != null) {
			fIndex.addChangeListener(l);
		}
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		if (fIndex != null) {
			fIndex.removeChangeListener(l);
		}
	}

	public ISVDBIndexCache getCache() {
		if (fIndex != null) {
			return fIndex.getCache();
		} else {
			return null;
		}
	}

	public void loadIndex(IProgressMonitor monitor) {
		if (fIndex != null) {
			fIndex.loadIndex(monitor);
		}
	}
	
	public boolean isLoaded() {
		if (fIndex != null) {
			return fIndex.isLoaded();
		} else {
			return true;
		}
	}
	
	public boolean isFileListLoaded() {
		if (fIndex != null) {
			return fIndex.isFileListLoaded();
		} else {
			return true;
		}
	}

	public SVDBIndexConfig getConfig() {
		if (fIndex != null) {
			return fIndex.getConfig();
		} else {
			return null;
		}
	}
	
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		List<SVDBIncFileInfo> ret = new ArrayList<SVDBIncFileInfo>();

		if (fIncFilesFinder != null) {
			ret.addAll(fIncFilesFinder.findIncludeFiles(root, flags));
		}
		
		if (fSuperIterator != null) {
			for (SVDBIncFileInfo inc_i : fSuperIterator.findIncludeFiles(root, flags)) {
				if (!ret.contains(inc_i)) {
					ret.add(inc_i);
				}
			}
		}
		
		return ret;
	}

	public void execOp(IProgressMonitor monitor, ISVDBIndexOperation op, boolean sync) {
		// First, run the operation on this index
		op.index_operation(monitor, this);
		
		if (fIndex != null) {
			fIndex.execOp(monitor, op, sync);
		}
		if (fSuperIterator != null) {
			fSuperIterator.execOp(monitor, op, sync);
		}
	}
	
}
