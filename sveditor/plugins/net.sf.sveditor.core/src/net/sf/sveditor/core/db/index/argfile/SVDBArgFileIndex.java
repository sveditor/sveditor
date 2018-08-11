/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.db.index.argfile;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.builder.ISVBuilderOutput;
import net.sf.sveditor.core.builder.SafeSVBuilderOutput;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBArgFile;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBDeclCacheFileAttr;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexStatsProvider;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBFileCacheData;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.index.SVDBFindIncFileUtils;
import net.sf.sveditor.core.db.index.SVDBIncFileInfo;
import net.sf.sveditor.core.db.index.SVDBIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBIndexChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexFactoryUtils;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexStats;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRefresh;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRemoveFiles;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.index.sv.SVDeclCacheBuilder;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec.NameMatchType;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.refs.SVDBFileRefFinder;
import net.sf.sveditor.core.db.refs.SVDBRefMatcher;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;

public class SVDBArgFileIndex implements 
		ISVDBIndex, ISVDBIndexInt,  
		ILogLevelListener, ILogLevel, ISVDBIndexStatsProvider,
		ISVDBDeclCacheInt {

	public String 								fProjectName;
	private IProject 							fProject;
	private String 								fBaseLocation;
	private String 								fResolvedBaseLocation;
	private String 								fBaseLocationDir;
	
	private SVDBArgFileIndexBuildData			fBuildData;
	private ISVDBIndexCacheMgr					fCacheMgr;

	private boolean 							fCacheDataValid;

	private List<ISVDBIndexChangeListener> 		fIndexChangeListeners;

	protected LogHandle fLog;
	private ISVDBFileSystemProvider 			fFileSystemProvider;

	private SVDBIndexConfig 					fConfig;

	private boolean 							fDebugEn;

	private boolean 							fInWorkspaceOk;

	/**
	 * True if the root file list is valid.
	 */
	private boolean								fIndexRefreshed;
	private boolean								fIndexValid;
	
	private ISVDBIndexBuilder					fIndexBuilder;
	private int									fInIndexOp;
	
	private SVDBArgFileParser					fArgFileParser;
	
	private ISVBuilderOutput					fOut;
	
	
	private SVDBArgFileIndex(String project) {
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		fProjectName = project;
		fLog = LogFactory.getLogHandle("SVDBArgFileIndex2");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();

		// Try to obtain the project handle
		try {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			fProject = root.getProject(fProjectName);
		} catch (IllegalStateException e) {
			// Occurs if the workspace is closed
		}
	}

	public SVDBArgFileIndex(
			String 						project, 
			String 						base_location,
			ISVDBFileSystemProvider 	fs_provider, 
			ISVDBIndexCache 			cache,
			SVDBIndexConfig 			config) {
		this(project);
		fBaseLocation = base_location;
		
		// Save this for later
		fCacheMgr = cache.getCacheMgr();
		fConfig = config;

		fBuildData = new SVDBArgFileIndexBuildData(
				cache, getBaseLocation(), null, null);
		fBuildData.setFSProvider(getFileSystemProvider());
		fBuildData.setProject(fProject);
		
		setFileSystemProvider(fs_provider);
		fInWorkspaceOk = (base_location.startsWith("${workspace_loc}"));
		
		fBuildData.setResolvedBaseLocation(getResolvedBaseLocation());
		fBuildData.setResolvedBaseLocationDir(getResolvedBaseLocationDir());
	
		fArgFileParser = new SVDBArgFileParser(
				getFileSystemProvider(),
				getBaseLocation(),
				getResolvedBaseLocation(),
				getResolvedBaseLocationDir(),
				fProject);
	}
	
	@Override
	public void dispose() {
		fLog.debug("dispose() - " + getBaseLocation());

		synchronized (fBuildData) {
			if (fBuildData.getCache() != null) {
				fBuildData.getCache().sync();
			}
			if (fFileSystemProvider != null) {
				fFileSystemProvider.dispose();
			}
		}
	}
	
	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		ISVDBIndexChangePlan plan = new SVDBIndexChangePlan(this, SVDBIndexChangePlanType.Empty);
		synchronized (fBuildData) {
			if (changes == null || !fIndexValid) {
				if (!fIndexValid) {
					plan =  new SVDBIndexChangePlanRebuild(this);
				}
			} else {
				plan = SVDBArgFileChangePlanner.createIndexChangePlan(this, fBuildData, changes);
			}
		}

		return plan;
	}

	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
		SafeSVBuilderOutput out = new SafeSVBuilderOutput(fOut);
		
	
		switch (plan.getType()) {
			case Refresh: {
				out.note("Refreshing index " + getBaseLocation() + " in project " + getProject());
				refresh_index(monitor);
			} break;
			
			case RebuildIndex: {
				out.note("Full build of index " + getBaseLocation() + " in project " + getProject());
				rebuild_index(monitor);
			} break;
			
			case RebuildFiles: {
				out.note("Incremental build of index " + getBaseLocation() + " in project " + getProject());
				rebuild_files(monitor, (SVDBIndexChangePlanRebuildFiles)plan);
			} break;
			
			case RemoveFiles: {
				remove_files(monitor, (SVDBIndexChangePlanRemoveFiles)plan);
			}
			
			default: {
				
			} break;
		}
		
		monitor.done();
	}

	/**
	 * TODO: move implementation outside?
	 * @param monitor
	 */
	@SuppressWarnings("unchecked")
	private void refresh_index(IProgressMonitor monitor) {
		SafeSVBuilderOutput out = new SafeSVBuilderOutput(fOut);
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Initialize index " + getBaseLocation(), 100);

		// Initialize the cache

		if (fCacheDataValid) {
			fCacheDataValid = checkCacheValid();
		}

		if (fCacheDataValid) {
			out.note("Cache is valid");
			if (fDebugEn) {
				fLog.debug("Cache is valid");
			}
			fIndexValid = true;

			// If we've determined the index data is valid, then we need to
			// fixup some index entries
			SVDBIndexCacheData cd = fBuildData.getIndexCacheData();

			if (cd.getFileCacheData() != null) { // ??
				for (SVDBFileCacheData file_data : cd.getFileCacheData().values()) {
					for (SVDBDeclCacheItem i : file_data.getTopLevelDeclarations()) {
						i.init(this);
					}
				}
			}

			// Also re-set filenames on the reference cache
			/** MSB:
			if (fBuildData.fIndexCacheData.getReferenceCacheMap() != null) {
				for (Entry<String, SVDBRefCacheEntry> e : 
					fBuildData.fIndexCacheData.getReferenceCacheMap().entrySet()) {
					e.getValue().setFilename(e.getKey());
				}
			}
			 */

			// Register all files with the directory set
			for (String f : fBuildData.getCache().getFileList(false)) {
				fBuildData.addFileDir(f);
			}
		} else {
			out.note("Cache is invalid");
			if (fDebugEn) {
				fLog.debug("Cache " + getBaseLocation() + " is invalid");
			}
		}
		// Not Needed: set the version to check later
//		fBuildData.fIndexCacheData.setVersion(SVCorePlugin.getVersion());
		
		fIndexRefreshed = true;
	}

	/**
	 * TODO: move implementation elsewhere?
	 * Note: test index hooks this method
	 * @param monitor
	 */
	protected void rebuild_index(IProgressMonitor monitor) {
		long start = System.currentTimeMillis();
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Rebuild " + getBaseLocation(), 10000);
		
//		if (!fIndexRefreshed) {
//			refresh_index(new NullProgressMonitor());
//		}

		ISVDBIndexCacheMgr c_mgr = fBuildData.getCacheMgr();
		SVDBArgFileIndexBuildData build_data = createBuildData();
		
		// Rebuild the index
		SVDBArgFileBuildUtils.buildIndex(
				subMonitor.newChild(9750), build_data, 
				this, fArgFileParser,
				new SafeSVBuilderOutput(fOut));		
		buildIndex(subMonitor.newChild(9750), build_data);
		
		if (fDebugEn) {
			// Show the index stats
			fLog.debug(LEVEL_MIN, "Index Stats " + getBaseLocation() + ":\n" + 
					build_data.getIndexStats().toString());
		}
		
		if (!subMonitor.isCanceled()) {
			// Apply the newly-built result
			synchronized (fBuildData) {
				fBuildData.apply(build_data);
			}
			
			// Notify clients that the index has new data
			synchronized (fIndexChangeListeners) {
				SVDBIndexChangeEvent ev = new SVDBIndexChangeEvent(
						SVDBIndexChangeEvent.Type.FullRebuild, this);
				for (int i=0; i<fIndexChangeListeners.size(); i++) {
					ISVDBIndexChangeListener l = fIndexChangeListeners.get(i);
					if (l == null) {
						fIndexChangeListeners.remove(i);
						i--;
					} else {
						l.index_event(ev);
					}
				}
			}
			
			fIndexValid = true;
		} else {
			build_data.dispose();
		}
		
		long end = System.currentTimeMillis();
	
		subMonitor.done();
	}

	/**
	 * TODO: move this to build utils?
	 * @param monitor
	 * @param plan
	 */
	private void rebuild_files(IProgressMonitor monitor, SVDBIndexChangePlanRebuildFiles plan) {
		SafeSVBuilderOutput out = new SafeSVBuilderOutput(fOut);
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "rebuild_files: " + plan.getFileListType());
		}
	
		SVDBArgFileIndexRebuilder.rebuild_files(
				this, 
				fBuildData,
				monitor,
				out,
				plan);
		
//		try {
//			// TODO: order files based on previous processing order
//			// Note: only important for MFCU mode
//
//			// TODO: determine whether these are SV are .f files?
//
//			
//			// Patch the new content into the index build data
//			synchronized (fBuildData) {
//
//				for (String path : file_list) {
//					// Remove this file from the 'existing' list
//					existing_files.remove(path);
//					
//					SubMonitor loopMonitor = subMonitor.newChild(1000);
//					loopMonitor.setTaskName("Merge " + path);
//					if (fDebugEn) {
//						fLog.debug("Merge: " + path);
//					}
//					SVDBFileTree     ft      = cache.getFileTree(new NullProgressMonitor(), path, false);
//					SVDBFile         file    = cache.getFile(new NullProgressMonitor(), path);
//					List<SVDBMarker> markers = cache.getMarkers(path);
//				
//					if (file != null) {
//						fBuildData.getCache().setFile(path, file, false);
//						if (ft != null) {
//							fBuildData.getCache().setFileTree(path, ft, false);
//						}
//						if (markers != null) {
//							fBuildData.getCache().setMarkers(path, markers, false);
//						}
//					} else {
//						System.out.println("File " + path + " doesn't exist " + fOut);
//						out.error("File " + path + " doesn't exist");
//					}
//
//					long last_modified = cache.getLastModified(path);
//					fBuildData.getCache().setLastModified(path, last_modified, false);
//			
//					int dst_id = fBuildData.mapFilePathToId(path, true);
//					int src_id = build_data.mapFilePathToId(path, false);
//					if (fDebugEn) {
//						fLog.debug("Note: Patch cache for " + path + " dst=" + dst_id + " src=" + src_id);
//						for (SVDBDeclCacheItem it : build_data.getIndexCacheData().getFileCacheData(src_id).getTopLevelDeclarations()) {
//							fLog.debug("  Item: " + it.getName());
//						}
//					}
//					fBuildData.getIndexCacheData().setFileCacheData(
//							dst_id, build_data.getIndexCacheData().getFileCacheData(src_id));
////					// All of these files (I think) will be root files
////			
////					if (ft != null) {
////						// Update the cached declarations
////						patch_decl_cache(ft, decl_cache, new_decl_cache);
////					}
//
//					loopMonitor.worked(1000);
//				}
//				
//				// Add any new files
//				for (String path : added_files) {
//					int attr = build_data.getFileAttr(path);
//					if (fDebugEn) {
//						fLog.debug("Add file \"" + path + "\" to cache");
//					}
//					fBuildData.addFile(path, attr);
//				}
//				
//				// TODO: collect declaration info from these files and remove
//				// from the declaration cache
//				for (String path : existing_files) {
//					if (fDebugEn) {
//						fLog.debug("Remove: " + path);
//					}
//					fBuildData.removeFile(path, false);
//				}
//			}
//		
//		} finally {
//			subMonitor.done();
//		}
	}
	
	void sendIndexChangeEv(SVDBIndexChangeEvent ev) {
		synchronized (fIndexChangeListeners) {
			if (fDebugEn) {
				fLog.debug("Notify listeners: ev= " + ev + " Listeners=" + fIndexChangeListeners.size());
			}
			for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
				l.index_event(ev);
			}
		}
	}

	/**
	 * Manages incrementally removing files from the index 
	 * @param plan
	 */
	private void remove_files(IProgressMonitor monitor, SVDBIndexChangePlanRemoveFiles plan) {
		SVDBIndexChangeEvent ev = null;
		SubMonitor subMonitor = SubMonitor.convert(monitor, plan.getFiles().size()*2);
		
		if (fDebugEn) {
			fLog.debug("--> remove_files " + plan.getFiles().size());
		}
		
		synchronized (fIndexChangeListeners) {
			if (fIndexChangeListeners.size() > 0) {
				ev = new SVDBIndexChangeEvent(
						SVDBIndexChangeEvent.Type.IncrRebuild, this);
			}
		}
		
		List<String> removed_root_files = new ArrayList<String>();
		List<String> root_files_to_reparse = new ArrayList<String>();
		
		for (String path : plan.getFiles()) {
			// First, determine if this is a root file. 
			// If so, then removing it is pretty simple
			if (fDebugEn) {
				fLog.debug("  path: " + path);
			}
			synchronized (fBuildData) {
				List<String> arg_files = fBuildData.getFileList(
						ISVDBDeclCache.FILE_ATTR_ARG_FILE);
				
				if (arg_files.contains(path)) {
					fLog.debug("Argument File: " + path);
					// Determine the set of source files contributed by 
					// the argument file
					SVDBFile argfile = fBuildData.getFile(new NullProgressMonitor(), path);
					
					if (argfile != null && argfile instanceof SVDBArgFile) {
						fArgFileParser.collectSourceFiles(
								fBuildData, (SVDBArgFile)argfile, removed_root_files);
					}
				} else {
					SVDBFileTree ft = SVDBArgFileBuildDataUtils.findRootFileTree(
							fBuildData, path);

					if (fDebugEn) {
						fLog.debug("  ft=" + ft);
					}

					if (ft != null) {
						if (ft.getFilePath().equals(path)) {
							// This is actually a root file
							removed_root_files.add(path);
						} else {
							// 
							if (!root_files_to_reparse.contains(path)) {
								root_files_to_reparse.add(path);
							}
						}
					} else {
						// See if this is an argument file
						SVDBArgFileBuildDataUtils.findContainingArgFile(
								fBuildData, path, true);
					}
				}
			}
			subMonitor.worked(1);
		}

		System.out.println("TODO: deal with removed files");
		synchronized (fBuildData) {
			for (String path : removed_root_files) {
				System.out.println("removeFile: " + path);
				fBuildData.removeFile(path, false);
			}
		}
		
		// Once everything is done, fire the index-change event
		if (ev != null) {
			synchronized (fIndexChangeListeners) {
				for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
					l.index_event(ev);
				}
			}
		}
		
		if (fDebugEn) {
			fLog.debug("<-- remove_files " + plan.getFiles().size());
		}
	}
	

	/**
	 * Patch the global declarations back into the main cache
	 * 
	 * TODO: move to a utilities class?
	 * 
	 * @param ft
	 * @param decl_cache
	 * @param new_decl_cache
	 */
	private static void patch_decl_cache(
			SVDBFileTree 							ft, 
			Map<String, List<SVDBDeclCacheItem>> 	decl_cache,
			Map<String, List<SVDBDeclCacheItem>>	new_decl_cache) {
		String path = ft.getFilePath();
		
		decl_cache.remove(path);
		
		if (new_decl_cache.containsKey(path)) {
			decl_cache.put(path, new_decl_cache.get(path));
		}
		
		// Now, recurse through the other included paths
		for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
			patch_decl_cache(ft_s, decl_cache, new_decl_cache);
		}
	}
	


	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	/**
	 * Called when the index is initialized to determine whether the cached
	 * information is still valid
	 * 
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private boolean checkCacheValid() {
		boolean valid = true;
		
		/* Filesystem is already versioned
		String version = SVCorePlugin.getVersion();

		if (fDebugEn) {
			fLog.debug("Cached version=" + fBuildData.fIndexCacheData.getVersion()
					+ " version=" + version);
		}

		if (fBuildData.fIndexCacheData.getVersion() == null
				|| !fBuildData.fIndexCacheData.getVersion().equals(version)) {
			valid = false;
			return valid;
		}
		 */

		if (fBuildData.getCache().getFileList(false).size() > 0) {
			for (String path : fBuildData.getCache().getFileList(false)) {
				long fs_timestamp = fFileSystemProvider.getLastModifiedTime(path);
				long cache_timestamp = fBuildData.getCache().getLastModified(path);
				if (fs_timestamp != cache_timestamp) {

					if (fDebugEn) {
						fLog.debug(LEVEL_MIN,
								"Cache is invalid due to timestamp on " + path
										+ ": file=" + fs_timestamp + " cache="
										+ cache_timestamp);
					}
					valid = false;
					break;
				}
			}
		} else {
			if (fDebugEn) {
				fLog.debug(LEVEL_MIN, "Cache " + getBaseLocation()
						+ " is invalid -- 0 entries");
			}
			SVDBIndexFactoryUtils.setBaseProperties(fConfig, this);
			valid = false;
		}

		// Seems messy
		if (fBuildData.getIndexCacheData().getMissingIncludeFiles().size() > 0 && valid) {
			if (fDebugEn) {
				fLog.debug("Checking missing-include list added files");
			}
			/** TODO: 
			for (String path : getCacheData().getMissingIncludeFiles()) {
				SVDBSearchResult<SVDBFile> res = findIncludedFile(path);
				if (res != null) {
					if (fDebugEn) {
						fLog.debug(
								LEVEL_MIN,
								"Cache "
										+ getBaseLocation()
										+ " is invalid since previously-missing include file is now found: "
										+ path);
					}
					valid = false;
					break;
				}
			}
			 */
		}

		if (valid) {
			synchronized (fBuildData) {
				for (String arg_file : fBuildData.getCache().getFileList(true)) {
					long ts = getFileSystemProvider().getLastModifiedTime(
							arg_file);
					long ts_c = fBuildData.getCache().getLastModified(arg_file);
					if (ts > ts_c) {
						fLog.debug("    arg_file " + arg_file + " ts=" + ts
								+ " cached ts=" + ts_c);
						return false;
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "[AbstractSVDBIndex] Cache "
					+ getBaseLocation() + " is "
					+ ((valid) ? "valid" : "invalid"));
		}

		return valid;
	}

	/**
	 * Initialize the index
	 * 
	 * @param monitor
	 */
	@Override
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		
		fIndexBuilder = builder;

		fBuildData.setIndexCacheData(new SVDBIndexCacheData(getBaseLocation()));
		fCacheDataValid = fBuildData.getCache().init(
				new NullProgressMonitor(), 
				fBuildData.getIndexCacheData(), 
				fBaseLocation);
		
		/** TODO: 
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRefresh plan = new SVDBIndexChangePlanRefresh(this);
			fIndexBuilder.build(plan);
		} else {
			// run the refresh in-line
			refresh_index(monitor);
		}
		 */

		monitor.done();
	}

	/**
	 * 
	 */
	@Override
	public void loadIndex(IProgressMonitor monitor) {
		
		if (fIndexBuilder != null) {
			ISVDBIndexBuildJob build_job = null;
			ensureIndexUpToDate(monitor);
			
			if (!fIndexRefreshed) {
				SVDBIndexChangePlanRefresh plan = new SVDBIndexChangePlanRefresh(this);
				build_job = fIndexBuilder.build(plan);
				build_job.waitComplete();
			}

			if (!fIndexValid) {
				// Schedule a job
				SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
				build_job = fIndexBuilder.build(plan);
				build_job.waitComplete();
			}
			fIndexValid = true;
		} else {
			if (!fIndexRefreshed) {
				refresh_index(new NullProgressMonitor());
			}
			if (!fIndexValid) {
				rebuild_index(new NullProgressMonitor());
			}
		}
	}

	@Override
	public boolean isLoaded() {
		return fIndexValid;
	}

	@Override
	public boolean isFileListLoaded() {
		return fIndexValid;
	}

	/**
	 * @param monitor
	 * @param state
	 */
	private void ensureIndexUpToDate(IProgressMonitor super_monitor) {
		SubMonitor subMonitor = SubMonitor.convert(super_monitor, "Ensure Index State for " + getBaseLocation(), 4);
	
		if (!fIndexValid || !fIndexRefreshed) {
			ISVDBIndexBuildJob build_job = null;
			
			if (fIndexBuilder != null) {
				// See if there is an active job 
				build_job = fIndexBuilder.findJob(this);
				
				if (build_job != null) {
					build_job.waitComplete();
				}
			} else {
//				System.out.println("[ERROR] no builder and invalid");
			}
		}

		subMonitor.done();
	}

	@Override
	public void rebuildIndex(IProgressMonitor monitor) {
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
			fIndexBuilder.build(plan);
		} else {
			// ??
		}
	}

	@Override
	public ISVDBIndexCache getCache() {
		return fBuildData.getCache();
	}

	@Override
	public SVDBIndexConfig getConfig() {
		return fConfig;
	}
	
	@Override
	public void setBuilderOutput(ISVBuilderOutput out) {
		fOut = out;
	}

	@Override
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
		fBuildData.setFSProvider(fs_provider);
		if (fArgFileParser != null) {
			fArgFileParser.setFileSystemProvider(fs_provider);
		}

		if (fFileSystemProvider != null) {
			fFileSystemProvider.init(getResolvedBaseLocationDir());
		}
	}

	@Override
	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}

	@Override
	public String getBaseLocation() {
		return fBaseLocation;
	}

	@Override
	public String getProject() {
		return fProjectName;
	}

	String getResolvedBaseLocation() {
		if (fResolvedBaseLocation == null) {
			fResolvedBaseLocation = SVDBIndexUtil.expandVars(fBaseLocation,
					fProjectName, fInWorkspaceOk);
			fResolvedBaseLocation = SVFileUtils.resolvePath(fResolvedBaseLocation, 
					getBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
		}

		return fResolvedBaseLocation;
	}
	
	String resolvePath(String path) {
		return SVFileUtils.resolvePath(path, 
				getResolvedBaseLocation(), 
				fFileSystemProvider,
				fInWorkspaceOk);
	}
	
	SVDBArgFileIndexBuildData createBuildData() {
		return createBuildData(fCacheMgr.createIndexCache(getProject(), getBaseLocation()));
	}
	
	SVDBArgFileIndexBuildData createBuildData(ISVDBIndexCache cache) {
		SVDBArgFileIndexBuildData build_data = new SVDBArgFileIndexBuildData(
				cache, getBaseLocation(), getResolvedBaseLocation(),
				getResolvedBaseLocationDir());
		build_data.setFSProvider(getFileSystemProvider());
		build_data.setProject(fProject);
		
		return build_data;
	}

	private String getResolvedBaseLocationDir() {
		if (fBaseLocationDir == null) {
			String base_location = getResolvedBaseLocation();
			if (fDebugEn) {
				fLog.debug("   base_location: " + base_location);
			}
			if (fFileSystemProvider.isDir(base_location)) {
				if (fDebugEn) {
					fLog.debug("       base_location + " + base_location
							+ " is_dir");
				}
				fBaseLocationDir = base_location;
			} else {
				if (fDebugEn) {
					fLog.debug("       base_location + " + base_location
							+ " not_dir");
				}
				fBaseLocationDir = SVFileUtils.getPathParent(base_location);
				if (fDebugEn) {
					fLog.debug("   getPathParent " + base_location + ": "
							+ fBaseLocationDir);
				}
			}
		}
		return fBaseLocationDir;
	}

	/**
	 * getFileList() -- returns a list of all source files
	 * TODO: Do we really need both methods?
	 */
	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		return getFileList(monitor, FILE_ATTR_SRC_FILE);
	}

	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		checkInIndexOp("getFileList");

		return fBuildData.getFileList(flags);
	}

	/**
	 * Implementation of ISVDBIndexIterator findFile()
	 */
	@Override
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		checkInIndexOp("findFile");
		
		synchronized (fBuildData) {
			return SVDBArgFileBuildDataUtils.findFile(fBuildData, monitor, path);
		}
	}

	/**
	 * Implementation of ISVDBIndexIterator method
	 */
	@Override
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		// TODO: Update implementation
		String r_path = path;
		SVDBFile file = null;
		
		checkInIndexOp("findPreProcFile");

		SVDBFileTree ft = SVDBArgFileBuildDataUtils.findTargetFileTree(fBuildData, r_path);
	
		if (ft != null) {
			file = ft.fSVDBFile;
		}

		return file;
	}

	@Override
	public boolean doesIndexManagePath(String path) {
		checkInIndexOp("findPreProcFile");
		
		path = SVFileUtils.resolvePath(path, getBaseLocation(), 
				fFileSystemProvider, fInWorkspaceOk);
	
		if (fBuildData.containsFile(path, FILE_ATTR_SRC_FILE)) {
			return true;
		} else if (fBuildData.containsFile(path, FILE_ATTR_ARG_FILE)) {
			return true;
		}
		
		return false;
	}

	@Override
	public List<SVDBMarker> getMarkers(String path) {
		checkInIndexOp("getMarkers");
		
		synchronized (fBuildData) {
			return SVDBArgFileBuildDataUtils.getMarkers(
					fBuildData, new NullProgressMonitor(), path);
		}
	}

	@Override
	public void addChangeListener(ISVDBIndexChangeListener l) {
		synchronized (fIndexChangeListeners) {
			fIndexChangeListeners.add(l);
		}
	}

	@Override
	public void removeChangeListener(ISVDBIndexChangeListener l) {
		synchronized (fIndexChangeListeners) {
			fIndexChangeListeners.remove(l);
		}
	}

	/**
	 * Note: this method is used by the editor to 
	 * update the file structure and markers based on the 
	 * current editor content
	 * 
	 * Returns <PreProc,PostProc> tuple
	 * 
	 * TODO: relocated implementation?
	 */
	@Override
	public Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor 	monitor,
			InputStream 		in, 
			String 				path, 
			List<SVDBMarker> 	markers) {
		Tuple<SVDBFile, SVDBFile> ret = null;
		
		if (markers == null) {
			markers = new ArrayList<SVDBMarker>();
		}
		
		synchronized (fBuildData) {
			String r_path = resolvePath(path);

			if (!fFileSystemProvider.fileExists(r_path)) {
				fLog.debug("parse: path " + r_path + " does not exist");
				return null;
			}
			

			checkInIndexOp("parse");

			
			
			int attr = fBuildData.getFileAttr(r_path);
			
			if ((attr & ISVDBDeclCacheFileAttr.FILE_ATTR_SV_FILE) != 0) {
				ret = parse_sv(monitor, fBuildData, in, r_path, markers);
			} else if ((attr & ISVDBDeclCacheFileAttr.FILE_ATTR_VH_FILE) != 0) {
				ret = parse_vh(monitor, fBuildData, in, r_path, markers);
			} else {
				System.out.println("Error: source language isn't specified for " + r_path);
			}
		}
		
		return ret;
	}
		
	private Tuple<SVDBFile, SVDBFile> parse_sv(
			IProgressMonitor 			monitor,
			SVDBArgFileIndexBuildData	build_data,
			InputStream 				in, 
			String 						r_path, 
			List<SVDBMarker> 			markers) {
		long start=0, end=0;
		SVDBFile file=null, file_ft=null;
		SVDeclCacheBuilder decl_builder = null; // TODO: new SVDeclCacheBuilder();
		//		decl_list, decl_cache, included_files, missing_includes, rootfile_id);

		//
		// TODO: using 'this' as the include provider 
		// may not be ideal
		SVPreProcessor preproc = new SVPreProcessor(
				r_path, in, fBuildData, fReadOnlyFileMapper);
		preproc.addListener(decl_builder);

		// TODO: collect macro definitions that came before this
		// NOTE: it's possible that this file shows up in multiple locations
		// Need to note this somehow?
		//
		// Need the ability to obtain all paths to this file:
		// - Starting with <path>, build vectors up to a root file
		// Should we worry about cross-index references?
		// TODO: add macros from FT
		List<SVDBMacroDef> incoming_macros = 
				SVDBArgFileBuildDataUtils.calculateIncomingMacros(
						fBuildData, r_path);
		end = System.currentTimeMillis();

		for (SVDBMacroDef m : incoming_macros) {
			preproc.setMacro(m);
		}

		fLog.debug("--> PreProcess " + r_path);
		start = System.currentTimeMillis();
		SVPreProcOutput out = preproc.preprocess();
		end = System.currentTimeMillis();
		fLog.debug("<-- PreProcess " + r_path + " " + (end-start) + "ms");

		SVParser f = new SVParser();
		f.setFileMapper(fReadOnlyFileMapper);

		SVDBFileTree ft = decl_builder.getFileTree();
		if (ft != null && ft.fMarkers != null) {
			for (SVDBMarker m : ft.fMarkers) {
				markers.add(m);
			}
		}

		fLog.debug("--> Parse " + r_path);
		SVLanguageLevel language_level;

		if (fBuildData.getForceSV()) {
			language_level = SVLanguageLevel.SystemVerilog;
		} else {
			language_level = SVLanguageLevel.computeLanguageLevel(r_path);
		}
		start = System.currentTimeMillis();
		file = f.parse(language_level, out, r_path, markers);
		int file_id = fBuildData.mapFilePathToId(r_path, false);
		file.setLocation(SVDBLocation.pack(file_id, 1, 0));

		//cleanExtFileElements(file_id, file);
		end = System.currentTimeMillis();
		fLog.debug("<-- Parse " + r_path + " " + (end-start) + "ms");
		file_ft = ft.getSVDBFile();
		return new Tuple<SVDBFile, SVDBFile>(file_ft, file);
	}
	
	private Tuple<SVDBFile, SVDBFile> parse_vh(
			IProgressMonitor 			monitor,
			SVDBArgFileIndexBuildData	build_data,
			InputStream 				in, 
			String 						r_path, 
			List<SVDBMarker> 			markers) {
		SVDBFile file=null, file_ft=null;
		System.out.println("TODO: parse VHDL");
		
		return new Tuple<SVDBFile, SVDBFile>(file_ft, file);
	}

	/**
	 * TODO: move implementation to a utilities class?
	 * 
	 * Note: This is used by IDE facilities that 
	 */
	@Override
	public ISVStringPreProcessor createPreProc(
			String 				path,
			InputStream			in,
			int					limit_lineno) {
		ISVStringPreProcessor ret = null;

		synchronized (fBuildData) {
			String r_path = resolvePath(path);

			if (!fFileSystemProvider.fileExists(r_path)) {
				fLog.debug("parse: path " + r_path + " does not exist");
				return null;
			}

			checkInIndexOp("parse");

			long start=0, end=0;
			
			if (fDebugEn) {
				start = System.currentTimeMillis();
			}
	
			if (fDebugEn) {
				end = System.currentTimeMillis();
				fLog.debug(LEVEL_MID, "  findTargetFileTree: " + (end-start) + "ms");
			}

			//
			// Note: Use the special read-only file mapper to 
			// ensure that the file map is not changed
			SVPreProcessor preproc = new SVPreProcessor(
					r_path, in, fBuildData, fReadOnlyFileMapper);

			// TODO: add macros from FT
			List<SVDBMacroDef> incoming_macros = 
					SVDBArgFileBuildDataUtils.calculateIncomingMacros(
							fBuildData, r_path);
			end = System.currentTimeMillis();
				
			for (SVDBMacroDef m : incoming_macros) {
				preproc.setMacro(m);
			}
			
			int this_fileid = fReadOnlyFileMapper.mapFilePathToId(r_path, false);
		
			// Collect local macros from 'input'
			preproc.preprocess();

			// How to handle this? 
			// Do we remove the macros that don't match?
			List<SVDBMacroDef> macros = new ArrayList<SVDBMacroDef>();
			for (SVDBMacroDef m : preproc.getDefaultMacros()) {
				if (m.getLocation() == -1 || limit_lineno == -1 ||
						SVDBLocation.unpackFileId(m.getLocation()) != this_fileid ||
						SVDBLocation.unpackLineno(m.getLocation()) <= limit_lineno) {
					macros.add(m);
				}
			}

			// No need to wrap anything up. 
			ret = preproc; // new SVStringPreProcessor(macros);
		}

		return ret;
	}

	/**
	 * Compute the include/list path to the specified file
	 * 
	 * This is used by IDE facilities that display the 
	 * path from an argument file to a specific file
	 */
	@Override
	public List<SVDBFilePath> getFilePath(String path) {
		List<SVDBFilePath> ret = new ArrayList<SVDBFilePath>();
		
		path = SVFileUtils.resolvePath(path, getBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
		
		boolean is_argfile = fBuildData.containsFile(path, ISVDBDeclCache.FILE_ATTR_ARG_FILE);
		SVDBFileTree ft = SVDBArgFileBuildDataUtils.findTargetFileTree(
				fBuildData, path);
		
		SVDBFilePath fp = new SVDBFilePath();
		if (ft != null) {
			String top_file_path = ft.getFilePath();
			fp.addPath(ft, null);

			if (!is_argfile) {
				// First, fill in the SV file structure
				while (ft.getParent() != null) {
					String child_path = ft.getFilePath();
					ft = ft.getParent();

					// Now, locate the statement used in include the file
					ISVDBItemBase inc_stmt = findIncStmt(ft.getSVDBFile(), child_path);
					fp.addPath(ft, inc_stmt);

					top_file_path = ft.getFilePath();
				}
			}
			
			// Now, move through the argument-file hierarchy
			Tuple<SVDBFileTree, ISVDBItemBase> af_it = 
					SVDBArgFileBuildDataUtils.findContainingArgFile(
					fBuildData, top_file_path, is_argfile);
			
			while (af_it != null) {
				fp.addPath(af_it.first(), af_it.second());
				
				af_it = SVDBArgFileBuildDataUtils.findContainingArgFile(
						fBuildData, af_it.first().getFilePath(), true);
			}
		}

		// Reverse the path, such that the target file is at the end
		for (int i=0; i<(fp.getPath().size()/2); i++) {
			Tuple<SVDBFileTree, ISVDBItemBase> i1, i2;
			i1 = fp.getPath().get(i);
			i2 = fp.getPath().get(fp.getPath().size()-i-1);
			
			fp.getPath().set(i, i2);
			fp.getPath().set(fp.getPath().size()-i-1, i1);
		}
		
		ret.add(fp);
		
		return ret;
	}

	/**
	 * TODO: relocate
	 * @param parent
	 * @param path
	 * @return
	 */
	private static ISVDBItemBase findIncStmt(ISVDBChildParent parent, String path) {
		ISVDBItemBase ret = null;
		String leaf = SVFileUtils.getPathLeaf(path);
		
		for (ISVDBChildItem it : parent.getChildren()) {
			if (it.getType() == SVDBItemType.Include) {
				SVDBInclude inc = (SVDBInclude)it;
				String inc_leaf = SVFileUtils.getPathLeaf(inc.getName());
			
				if (inc_leaf.equals(leaf)) {
					ret = it;
					break;
				}
			} else if (it instanceof ISVDBChildParent) {
				// Search down
				if ((ret = findIncStmt((ISVDBChildParent)it, path)) != null) {
					break;
				}
			}
		}
		
		return ret;
	}

	/**
	 * TODO: need both flavors?
	 */
	@Override
	public SVDBFile findFile(String path) {
		return findFile(new NullProgressMonitor(), path);
	}

	@Override
	public SVDBFile findPreProcFile(String path) {
		return findPreProcFile(new NullProgressMonitor(), path);
	}

	@Override
	public SVDBFileTree findFileTree(
			String 		path,
			boolean 	is_argfile) {
		
		checkInIndexOp("findFileTree");

		SVDBFileTree ft = null;
		synchronized (fBuildData) {
			ft = fBuildData.getCache().getFileTree(
					new NullProgressMonitor(), path, is_argfile);
		}

		return ft;
	}


	@Override
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		checkInIndexOp("findPackageDecl");
		
		return SVDBArgFileBuildDataUtils.findPackageDecl(
				fBuildData, monitor, pkg_item);
	}

	@Override
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor 		monitor, 
			String 					name, 
			ISVDBFindNameMatcher 	matcher) {
		
		checkInIndexOp("findGlobalScopeDecl");
	
		return SVDBArgFileBuildDataUtils.findGlobalScopeDecl(
				fBuildData, monitor, name, matcher);
	}

	@Override
	public void findReferences(
			IProgressMonitor 		monitor,
			ISVDBRefSearchSpec		ref_spec,
			ISVDBRefVisitor			ref_visitor) {
		checkInIndexOp("findReferences");

		Set<Integer> root_files = new HashSet<Integer>();
		for (SVDBFileCacheData d : fBuildData.getIndexCacheData().getRootFileCacheData().values()) {
			if (d.getRefCache().contains(ref_spec.getName())) {
				// TODO: change caching scheme to be per-file
				// Now, have a closer look
				if (ref_spec.getNameMatchType() == NameMatchType.Equals) {
					
					// First, process the root file
					String root_filename = fBuildData.mapFileIdToPath(d.getFileId());
					SVDBFile root_file = fBuildData.getCache().getFile(
							new NullProgressMonitor(), root_filename);
					
					if (root_file != null) {
						SVDBRefMatcher ref_matcher = new SVDBRefMatcher(ref_spec, ref_visitor);
						SVDBFileRefFinder finder = new SVDBFileRefFinder();
						finder.setRefVisitor(ref_matcher);
						finder.visit(root_file);
					}
				} else if (ref_spec.getNameMatchType() == NameMatchType.MayContain) {
					// TODO: ??
					// Caller is simply interested in whether there might be a match
//					if (file_list.size() > 0) {
//						ref_visitor.visitRef(ref_spec, null);
//					}
				}				
			}
		}
	}

	@Override
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		
		checkInIndexOp("getDeclFile");

		SVDBFile file = null;
		
		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = SVDBArgFileBuildDataUtils.findTargetFileTree(
					fBuildData, 
					fBuildData.mapFileIdToPath(item.getFileId()));
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
			file = findFile(fBuildData.mapFileIdToPath(item.getFileId()));
		}

		return file;
	}

	// FIXME:
	@Override
	public SVDBFile getDeclFilePP(
			IProgressMonitor 		monitor,
			SVDBDeclCacheItem 		item) {
		checkInIndexOp("getDeclFilePP");

		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findFileTree(
					fBuildData.mapFileIdToPath(item.getFileId()), false);
			if (ft != null) {
				file = ft.getSVDBFile();
			}
		} else {
			file = findFile(
					fBuildData.mapFileIdToPath(item.getFileId()));
		}

		return file;
	}

	// Implementation of ISVDBDeclCacheInt
	@Override
	public ISVDBDeclCache getDeclCache() {
		return this;
	}
	
	@Override
	public SVDBFile getDeclRootFile(SVDBDeclCacheItem item) {
		String rootfile_p = mapFileIdToPath(item.getRootFileId());
		SVDBFile ret = fBuildData.getFile(new NullProgressMonitor(), rootfile_p);
		
		return ret;
	}
	
	@Override
	public SVDBFileTree getDeclRootFileTree(SVDBDeclCacheItem item) {
		String rootfile_p = mapFileIdToPath(item.getRootFileId());
		return fBuildData.getCache().getFileTree(new NullProgressMonitor(), rootfile_p, false);
	}
	
	@Override
	public String mapFileIdToPath(int id) {
		return fBuildData.mapFileIdToPath(id);
	}
	
	@Override
	public List<SVDBDeclCacheItem> getScope(int rootfile_id, List<Integer> scope) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		SVDBFileCacheData root_data = 
				fBuildData.getIndexCacheData().getFileCacheData(rootfile_id);
		
		for (int decl_id : scope) {
			ret.add(root_data.getTopLevelDeclarations().get(decl_id));
		}
		
		return ret;
	}

	@Override
	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}
	
	/**
	 * Build all the files in the index
	 * 
	 * Note: test indexes hook this method
	 * 
	 * @param monitor
	 * @param build_data
	 */
	protected void buildIndex(
			IProgressMonitor 				monitor,
			SVDBArgFileIndexBuildData		build_data) {
		SVDBArgFileBuildUtils.buildIndex(
				monitor, build_data, this, fArgFileParser,
				new SafeSVBuilderOutput(fOut));
	}

	@Override
	public ISVPreProcessor createPreProcScanner(String path) {
		SVPreProcessor ret = null;
		
		path = SVFileUtils.resolvePath(path, getBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
		
		checkInIndexOp("createPreProcScanner");
		SVDBFileTree ft = SVDBArgFileBuildDataUtils.findTargetFileTree(
				fBuildData, path);
		
		if (ft != null) {
			List<SVDBFileTree> ft_l = new ArrayList<SVDBFileTree>();
		
			InputStream in = fFileSystemProvider.openStream(path);
			ret = new SVPreProcessor(ft.getFilePath(), in, null, null);
			
			while (ft != null) {
				ft_l.add(ft);
				ft = (SVDBFileTree)ft.fParent;
			}

			// Do not include macros from the target file
			for (int i=ft_l.size()-1; i>=1; i--) {
				SVDBFileTree ft_t = ft_l.get(i);
				for (Entry<String, String> e : ft_t.fReferencedMacros.entrySet()) {
					ret.setMacro(e.getKey(), e.getValue());
				}
			}
		} else {
			System.out.println("Error: failed to find target filetree for " + path);
		}

		return ret;
	}

	@Override
	public String getFileFromId(int fileid) {
		return fBuildData.mapFileIdToPath(fileid);
	}

	@Override
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		checkInIndexOp("findIncludeFiles");
		
		return SVDBFindIncFileUtils.findIncludeFiles(
				this,
				fFileSystemProvider,
				fBuildData.getIncludePathList(),
				root, flags);
	}

	/**
	 * Implement of ISVDBIndexOperationRunner
	 */
	@Override
	public void execOp(
			IProgressMonitor 		monitor, 
			ISVDBIndexOperation 	op,
			boolean					sync) {
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

	/**
	 * Note: called by a test
	 * @return
	 */
	@Override
	public SVDBIndexStats getIndexStats() {
		return fBuildData.getIndexStats();
	}

	private boolean checkInIndexOp(String name) {
		if (fInIndexOp == 0) {
			/** Ignore for now
			Exception ex = null;
			try {
				throw new Exception();
			} catch (Exception e) {
				ex = e;
			}
			fLog.error(name + " called from outside index operation", ex);
			 */
			return false;
		} else {
			return true;
		}
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		synchronized (fBuildData) {
			List<String> files = fBuildData.getFileList(
					FILE_ATTR_SRC_FILE+FILE_ATTR_ROOT_FILE);
			
			// Iterate through files, then contents
			for (String file : files) {
				SVDBFile svdb_f = fBuildData.getFile(
						new NullProgressMonitor(), file);
				svdb_f.accept(v);
			}
		}
	}



	private ISVPreProcFileMapper fReadOnlyFileMapper = new ISVPreProcFileMapper() {
		
		public int mapFilePathToId(String path, boolean add) {
			return fBuildData.mapFilePathToId(path, false);
		}
		
		public String mapFileIdToPath(int id) {
			return fBuildData.mapFileIdToPath(id);
		}
	};


}
