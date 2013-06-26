/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.db.index.argfile;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexFactoryUtils;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRefresh;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache.FileType;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.refs.ISVDBRefFinder;
import net.sf.sveditor.core.db.refs.ISVDBRefMatcher;
import net.sf.sveditor.core.db.refs.SVDBRefCacheEntry;
import net.sf.sveditor.core.db.refs.SVDBRefCacheItem;
import net.sf.sveditor.core.db.refs.SVDBRefFinder;
import net.sf.sveditor.core.db.refs.SVDBRefItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBArgFileIndex2 implements 
		ISVDBIndex, ISVDBIndexInt, ISVDBRefFinder, 
		ILogLevelListener, ILogLevel {

	public String 								fProjectName;
	private IProject 							fProject;
	private String 								fBaseLocation;
	private String 								fResolvedBaseLocation;
	private String 								fBaseLocationDir;
	
	private SVDBArgFileIndexBuildData			fBuildData;
	private ISVDBIndexCacheMgr					fCacheMgr;

	private boolean 							fCacheDataValid;

	private List<ISVDBIndexChangeListener> 		fIndexChangeListeners;

	private LogHandle fLog;
	private ISVDBFileSystemProvider 			fFileSystemProvider;

	private SVDBIndexConfig 					fConfig;

	private boolean 							fDebugEn;

	private boolean 							fInWorkspaceOk;

	/**
	 * True if the root file list is valid.
	 */
	private boolean								fIndexValid;
	private boolean 							fAutoRebuildEn;
	private boolean 							fIsDirty;
	
	private ISVDBIndexBuilder					fIndexBuilder;
	private int									fInIndexOp;
	
	
	private SVDBArgFileIndex2(String project) {
		fIndexChangeListeners = new ArrayList<ISVDBIndexChangeListener>();
		fProjectName = project;
		fLog = LogFactory.getLogHandle("SVDBArgFileIndex2");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		fAutoRebuildEn = true;

		// Try to obtain the project handle
		try {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			fProject = root.getProject(fProjectName);
		} catch (IllegalStateException e) {
			// Occurs if the workspace is closed
		}
	}

	public SVDBArgFileIndex2(
			String 						project, 
			String 						base_location,
			ISVDBFileSystemProvider 	fs_provider, 
			ISVDBIndexCache 			cache,
			SVDBIndexConfig 			config) {
		this(project);
		fBaseLocation = base_location;
		fBuildData = new SVDBArgFileIndexBuildData(cache, base_location);
		
		// Save this for later
		fCacheMgr = cache.getCacheMgr();
		fConfig = config;

		setFileSystemProvider(fs_provider);
		fInWorkspaceOk = (base_location.startsWith("${workspace_loc}"));
		fAutoRebuildEn = true;
	}
	
	public void setIndexBuilder(ISVDBIndexBuilder builder) {
		fIndexBuilder = builder;
	}

	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		ISVDBIndexChangePlan plan = new SVDBIndexChangePlan(this, SVDBIndexChangePlanType.Empty);
		
		
		if (changes == null || !fIndexValid) {
//			System.out.println("changes=" + changes + " fIndexValid=" + fIndexValid);
			if (!fIndexValid) {
				// Return a 'build me' plan, since we're not valid
				plan = new SVDBIndexChangePlanRebuild(this);
			}
		} else {
			synchronized (fBuildData) {
				List<String> changed_sv_files = new ArrayList<String>();
				List<String> changed_f_files = new ArrayList<String>();
				
				SVDBIndexChangePlanRebuildFiles rebuild_sv_files_plan = new SVDBIndexChangePlanRebuildFiles(this);
				SVDBIndexChangePlanRebuildFiles rebuild_arg_files_plan = new SVDBIndexChangePlanRebuildFiles(this);
				
				for (SVDBIndexResourceChangeEvent ev : changes) {
					String path = SVFileUtils.resolvePath(ev.getPath(), getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
//					System.out.println("incremental rebuild: " + path);
					if (fBuildData.fIndexCacheData.fSrcFileList.contains(path)) {
						if (!changed_sv_files.contains(path)) {
							changed_sv_files.add(path);
						}
					} else if (fBuildData.fIndexCacheData.fArgFilePaths.contains(path)) {
						// Argument file changed, so rebuild project
						if (!changed_f_files.contains(path)) {
							changed_f_files.add(path);
						}
						break;
					}
				}
				
				if (changed_f_files.size() > 0) {
					// TODO: Full build for now
					plan = new SVDBIndexChangePlanRebuild(this);
				} else if (changed_sv_files.size() > 0) {
					plan = create_incr_plan(changed_sv_files);
				}
			}
		}
		
		return plan;
	}

	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
	
		switch (plan.getType()) {
			case Refresh: {
				refresh_index(monitor);
			} break;
			
			case RebuildIndex: {
				rebuild_index(monitor);
			} break;
			
			case RebuildFiles: {
				rebuild_files(monitor, (SVDBIndexChangePlanRebuildFiles)plan);
			} break;
			
			default: {
				
			} break;
		}
		
		monitor.done();
	}

	@SuppressWarnings("unchecked")
	private void refresh_index(IProgressMonitor monitor) {
		monitor.beginTask("Initialize index " + getBaseLocation(), 100);

		// Initialize the cache
		IProgressMonitor m = new SubProgressMonitor(monitor, 1);

		if (fCacheDataValid) {
			fCacheDataValid = checkCacheValid();
		}

		if (fCacheDataValid) {
			if (fDebugEn) {
				fLog.debug("Cache is valid");
			}
			fIndexValid = true;

			// If we've determined the index data is valid, then we need to
			// fixup some index entries
			if (fBuildData.fIndexCacheData.getDeclCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : fBuildData.getDeclCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}

			// Also update the package cache
			if (fBuildData.fIndexCacheData.getPackageCacheMap() != null) {
				for (Entry<String, List<SVDBDeclCacheItem>> e : 
						fBuildData.fIndexCacheData.getPackageCacheMap().entrySet()) {
					for (SVDBDeclCacheItem i : e.getValue()) {
						i.init(this);
					}
				}
			}

			// Also re-set filenames on the reference cache
			if (fBuildData.fIndexCacheData.getReferenceCacheMap() != null) {
				for (Entry<String, SVDBRefCacheEntry> e : 
					fBuildData.fIndexCacheData.getReferenceCacheMap().entrySet()) {
					e.getValue().setFilename(e.getKey());
				}
			}

			// Register all files with the directory set
			for (String f : fBuildData.fCache.getFileList(false)) {
				addFileDir(fBuildData, f);
			}
		} else {
			if (fDebugEn) {
				fLog.debug("Cache " + getBaseLocation() + " is invalid");
			}
			invalidateIndex(m, "Cache is invalid", true);
		}
		// Not Needed: set the version to check later
//		fBuildData.fIndexCacheData.setVersion(SVCorePlugin.getVersion());

		// Set the global settings anyway
		if (fConfig != null
				&& fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
			Map<String, String> define_map = (Map<String, String>) fConfig
					.get(ISVDBIndexFactory.KEY_GlobalDefineMap);

			fBuildData.fIndexCacheData.clearGlobalDefines();
			for (String key : define_map.keySet()) {
				fBuildData.fIndexCacheData.setGlobalDefine(key, define_map.get(key));
			}
		}		
	}
	
	private void rebuild_index(IProgressMonitor	monitor) {
		ISVDBIndexCache new_cache = 
				fBuildData.fCacheMgr.createIndexCache(getProject(), getBaseLocation());
		SVDBArgFileIndexBuildData build_data = new SVDBArgFileIndexBuildData(
				new_cache, getBaseLocation());
		
		synchronized (fBuildData) {
			// Copy in relevant information
			build_data.getGlobalDefines().putAll(fBuildData.getGlobalDefines());
			build_data.fFileSystemProvider = fFileSystemProvider;
		}
	
		monitor.beginTask("Rebuild " + getBaseLocation(), 10000);

		// Rebuild the index
		buildIndex(new SubProgressMonitor(monitor, 9750), build_data);
		
		if (!monitor.isCanceled()) {
			// Apply the newly-built result
			synchronized (fBuildData) {
				fBuildData.apply(build_data);
			}
			
			// Notify clients that the index has new data
			synchronized (fIndexChangeListeners) {
				for (ISVDBIndexChangeListener l : fIndexChangeListeners) {
					l.index_rebuilt();
				}
			}
			
			fIndexValid = true;
		} else {
			build_data.dispose();
		}
	
		monitor.done();
	}

	/**
	 * Rebuild 
	 * @param monitor
	 * @param plan
	 */
	private void rebuild_files(IProgressMonitor monitor, SVDBIndexChangePlanRebuildFiles plan) {
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "rebuild_files: ");
		}
		
		monitor.beginTask("Update " + getBaseLocation(), 2*1000*plan.getFileList().size());
	
		ISVDBIndexCache cache = fCacheMgr.createIndexCache(getProject(), getBaseLocation());
		SVDBArgFileIndexBuildData build_data = new SVDBArgFileIndexBuildData(cache, getBaseLocation());
		build_data.fFileSystemProvider = fFileSystemProvider;
		
		synchronized (fBuildData) {
			// Must initialize the file mapper state so any
			// new files are given correct numberings
			build_data.initFileMapperState(fBuildData);
		}
	
		// Save the number of files pre, so we can update post
		int n_files_pre = build_data.fIndexCacheData.fSrcFileList.size();
	
		try {
			// TODO: order files based on previous processing order
			// Note: only important for MFCU mode

			// TODO: determine whether these are SV are .f files?
			for (String path : plan.getFileList()) {
				monitor.subTask("Parse " + path);
				// path is a 'root' file
				InputStream in = fFileSystemProvider.openStream(path);
				
				if (in == null) {
					continue;
				}
				
				SVPreProcessor2 preproc = new SVPreProcessor2(
						path, in, build_data, build_data);
				
				synchronized (fBuildData) {
					if (fBuildData.isMFCU()) {
						List<SVDBMacroDef> macros = calculateIncomingMacros(fBuildData, path);

						for (SVDBMacroDef d : macros) {
							preproc.setMacro(d);
						}
					} else {
						// Add global defines
						for (Entry<String, String> e : fBuildData.getDefines().entrySet()) {
							preproc.setMacro(new SVDBMacroDef(e.getKey(), e.getValue()));
						}
						for (Entry<String, String> e : build_data.getGlobalDefines().entrySet()) {
							preproc.setMacro(new SVDBMacroDef(e.getKey(), e.getValue()));
						}							
					}
				}
				
				SVPreProcOutput out = preproc.preprocess();
				SVDBFileTree ft = out.getFileTree();
				
				ParserSVDBFileFactory f = new ParserSVDBFileFactory();
				f.setFileMapper(build_data);
				
				SVLanguageLevel language_level = SVLanguageLevel.computeLanguageLevel(path);
				List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
				SVDBFile file = f.parse(language_level, out, path, markers);
				
				// Now, set the new root-file info to the cache
				build_data.fCache.setFile(path, file, false);
				build_data.fCache.setFileTree(path, ft, false);
				build_data.fCache.setMarkers(path, markers, false);
				long last_modified = fFileSystemProvider.getLastModifiedTime(path);
				build_data.fCache.setLastModified(path, last_modified, false);
				
				cacheDeclarations(build_data, file, ft);
				
				monitor.worked(1000);
			}
			
			// Patch the new content into the index build data
			synchronized (fBuildData) {
				Map<String, List<SVDBDeclCacheItem>> decl_cache = fBuildData.getDeclCacheMap();
				Map<String, List<SVDBDeclCacheItem>> new_decl_cache = build_data.getDeclCacheMap();
				
					
				for (String path : plan.getFileList()) {
					monitor.subTask("Merge " + path);
					SVDBFileTree     ft      = cache.getFileTree(new NullProgressMonitor(), path, false);
					SVDBFile         file    = cache.getFile(new NullProgressMonitor(), path);
					List<SVDBMarker> markers = cache.getMarkers(path);
				
					if (file != null) {
						fBuildData.fCache.setFile(path, file, false);
					} else {
						System.out.println("[ERROR] file " + path + " is null");
					}
					if (ft != null) {
						fBuildData.fCache.setFileTree(path, ft, false);
					} else {
						System.out.println("[ERROR] ft " + path + " is null");
					}
					if (markers != null) {
						fBuildData.fCache.setMarkers(path, markers, false);
					} else {
						System.out.println("[ERROR] markers " + path + " is null");
					}
				
					long last_modified = cache.getLastModified(path);
					fBuildData.fCache.setLastModified(path, last_modified, false);
					
					// Update the cached declarations
					patch_decl_cache(ft, decl_cache, new_decl_cache);

					monitor.worked(1000);
				}
				
				// Add any new files
				List<String> new_src_files = build_data.fIndexCacheData.fSrcFileList;
				if (n_files_pre < new_src_files.size()) {
					for (int i=n_files_pre-1; i<new_src_files.size(); i++) {
						fBuildData.fIndexCacheData.fSrcFileList.add(new_src_files.get(i));
					}
				}
			}
		} finally {
			// No matter what, need to dispose of the new cache
			if (cache != null) {
				cache.dispose();
			}
			monitor.done();
		}
	}

	/**
	 * Patch the global declarations back into the main cache
	 * 
	 * @param ft
	 * @param decl_cache
	 * @param new_decl_cache
	 */
	private void patch_decl_cache(
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
	
	private ISVDBIndexChangePlan create_incr_plan(List<String> changed_sv_files) {
		SVDBIndexChangePlanRebuildFiles plan = new SVDBIndexChangePlanRebuildFiles(this);
	
		for (String sv_path : changed_sv_files) {
			SVDBFileTree ft = findRootFileTree(fBuildData, sv_path);
			if (ft != null) {
				plan.addFile(ft.getFilePath());
			}
		}
		
		return plan;
	}

	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	public void setEnableAutoRebuild(boolean en) {
		fAutoRebuildEn = en;
	}

	public boolean isDirty() {
		return fIsDirty;
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

		// Confirm that global defines are the same
		if (fConfig != null) {
			// First check to see if all configured global defines are present
			if (fConfig.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
				Map<String, String> define_map = (Map<String, String>) fConfig
						.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
				if (define_map.size() != fBuildData.getGlobalDefines()
						.size()) {
					if (fDebugEn) {
						fLog.debug(LEVEL_MID,
								"Cache invalid -- size of global defines is different");
					}
					valid = false;
				} else {
					// Check all defines
					for (Entry<String, String> e : define_map.entrySet()) {
						if (fBuildData.getGlobalDefines().containsKey(
								e.getKey())) {
							if (!fBuildData.getGlobalDefines()
									.get(e.getKey()).equals(e.getValue())) {
								if (fDebugEn) {
									fLog.debug(
											LEVEL_MID,
											"Cache invalid -- define "
													+ e.getKey()
													+ " has a different value");
								}
								valid = false;
								break;
							}
						} else {
							if (fDebugEn) {
								fLog.debug(LEVEL_MID,
										"Cache invalid -- define " + e.getKey()
												+ " not in cache");
							}
							valid = false;
							break;
						}
					}
				}
			} else if (fBuildData.getGlobalDefines().size() > 0) {
				// Local index has defines and the incoming config does not
				if (fDebugEn) {
					fLog.debug(LEVEL_MID,
							"Cache invalid -- no global defines, and cache has");
				}
				valid = false;
			}
		}

		if (fBuildData.fCache.getFileList(false).size() > 0) {
			for (String path : fBuildData.fCache.getFileList(false)) {
				long fs_timestamp = fFileSystemProvider.getLastModifiedTime(path);
				long cache_timestamp = fBuildData.fCache.getLastModified(path);
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

		if (getCacheData().getMissingIncludeFiles().size() > 0 && valid) {
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
				for (String arg_file : fBuildData.fCache.getFileList(true)) {
					long ts = getFileSystemProvider().getLastModifiedTime(
							arg_file);
					long ts_c = fBuildData.fCache.getLastModified(arg_file);
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
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		SubProgressMonitor m;
		
		fIndexBuilder = builder;

		fBuildData.fIndexCacheData = new SVDBArgFileIndexCacheData(getBaseLocation());
		fCacheDataValid = fBuildData.fCache.init(
				new NullProgressMonitor(), 
				fBuildData.fIndexCacheData, 
				fBaseLocation);
		
		/** TODO: 
		 */
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRefresh plan = new SVDBIndexChangePlanRefresh(this);
			fIndexBuilder.build(plan);
		} else {
			// run the refresh in-line
			refresh_index(monitor);
		}

		monitor.done();
	}

	/**
	 * 
	 */
	public void loadIndex(IProgressMonitor monitor) {
		
		if (fIndexBuilder != null) {
			ensureIndexUpToDate(monitor);
		} else {
			if (!fIndexValid) {
				rebuild_index(new NullProgressMonitor());
			}
		}
	}

	public boolean isLoaded() {
		return fIndexValid;
	}

	public boolean isFileListLoaded() {
		return fIndexValid;
	}

	/**
	 * @param monitor
	 * @param state
	 */
	private void ensureIndexUpToDate(IProgressMonitor super_monitor) {
		SubProgressMonitor monitor = new SubProgressMonitor(super_monitor, 1);
		monitor.beginTask("Ensure Index State for " + getBaseLocation(), 4);

		if (!fIndexValid) {
			SVDBIndexBuildJob build_job = null;
			
			if (fIndexBuilder != null) {
				// See if there is an active job 
				build_job = fIndexBuilder.findJob(this);
				
				if (build_job != null) {
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
//				System.out.println("[ERROR] no builder and invalid");
			}
		}

		monitor.done();
	}

	private void invalidateIndex(IProgressMonitor monitor, String reason,
			boolean force) {
		if (fDebugEn) {
			if (fAutoRebuildEn || force) {
				fLog.debug(LEVEL_MIN, "InvalidateIndex: "
						+ ((reason == null) ? "No reason given" : reason));
			} else {
				fLog.debug(LEVEL_MIN, "InvalidateIndex: "
						+ ((reason == null) ? "No reason given" : reason)
						+ " (ignored -- AutoRebuild disabled)");
			}
		}

		/** TODO:
		synchronized (this) {
			if (fAutoRebuildEn || force) {
				fIndexValid = false;
				fCacheDataValid = false;
				fIndexCacheData.clear();
				fCache.clear(monitor);
				fMissingIncludes.clear();
			} else {
				fIsDirty = true;
			}
		}
		 */
	}

	public void rebuildIndex(IProgressMonitor monitor) {
		if (fIndexBuilder != null) {
			SVDBIndexChangePlanRebuild plan = new SVDBIndexChangePlanRebuild(this);
			fIndexBuilder.build(plan);
		} else {
			invalidateIndex(monitor, "Rebuild Index Requested", true);
		}
	}

	public ISVDBIndexCache getCache() {
		return fBuildData.fCache;
	}

	public SVDBIndexConfig getConfig() {
		return fConfig;
	}

	private SVDBBaseIndexCacheData getCacheData() {
		return fBuildData.fIndexCacheData;
	}

	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFileSystemProvider = fs_provider;
		fBuildData.fFileSystemProvider = fs_provider;

		if (fFileSystemProvider != null) {
			fFileSystemProvider.init(getResolvedBaseLocationDir());
		}
	}

	public ISVDBFileSystemProvider getFileSystemProvider() {
		return fFileSystemProvider;
	}

	public String getBaseLocation() {
		return fBaseLocation;
	}

	public String getProject() {
		return fProjectName;
	}

	public IProject getProjectHndl() {
		return fProject;
	}

	public String getResolvedBaseLocation() {
		if (fResolvedBaseLocation == null) {
			fResolvedBaseLocation = SVDBIndexUtil.expandVars(fBaseLocation,
					fProjectName, fInWorkspaceOk);
		}

		return fResolvedBaseLocation;
	}

	public String getResolvedBaseLocationDir() {
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

	public void setGlobalDefine(String key, String val) {
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "setGlobalDefine(" + key + ", " + val + ")");
		}
		fBuildData.fIndexCacheData.setGlobalDefine(key, val);

		// Rebuild the index when something changes
		/** TODO:
		if (!fIndexCacheData.getGlobalDefines().containsKey(key)
				|| !fIndexCacheData.getGlobalDefines().get(key).equals(val)) {
			rebuildIndex(new NullProgressMonitor());
		}
		 */
	}

	public void clearGlobalDefines() {
		fBuildData.fIndexCacheData.clearGlobalDefines();
		/** TODO: should queue for rebuild?
		 */
	}

	/**
	 * getFileList() -- returns a list of all source files
	 */
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		checkInIndexOp("getFileList");

		List<String> ret = new ArrayList<String>();
		synchronized (fBuildData) {
			ret.addAll(fBuildData.fIndexCacheData.fSrcFileList);
		}
		
		return ret;
	}

	/**
	 * Implementation of ISVDBIndexIterator findFile()
	 */
	public SVDBFile findFile(IProgressMonitor monitor, String path) {
		String r_path = path;
		SVDBFile ret = null;
		if (fDebugEn) {
			fLog.debug("--> findFile: " + path);
		}
		
		checkInIndexOp("findFile");
		
		ISVDBIndexCache.FileType ft = fBuildData.fCache.getFileType(r_path);
		
		if (ft == FileType.ArgFile) {
			// Just return the file
			synchronized (fBuildData) {
				ret = fBuildData.fCache.getFile(new NullProgressMonitor(), r_path);
			}
		} else {
			// We assume the file is SystemVerilog
			int id = fBuildData.mapFilePathToId(r_path, false);
			
			// See if we can find the root file
			String root_path = findRootFilePath(fBuildData, r_path);
			
			if (root_path != null) {
				// Get the FileMap
				Map<Integer, SVDBFile> map = fBuildData.fCache.getSubFileMap(root_path);
				
				if (map == null) {
					// re-create the map
					SVDBFile file = fBuildData.fCache.getFile(new NullProgressMonitor(), root_path);
					map = new HashMap<Integer, SVDBFile>();
				
					SVDBFile f = new SVDBFile(root_path);
					map.put(id, f);
					long start = System.currentTimeMillis();
					createSubFileMap(fBuildData, map, file, id, f);
					long end = System.currentTimeMillis();
					fBuildData.fCache.setSubFileMap(root_path, map);
				}
				
				ret = map.get(id);
			}
		}

		monitor.done();

		if (fDebugEn) {
			fLog.debug("<-- findFile: " + path + " ret=" + ret);
		}

		return ret;
	}
	
	private void createSubFileMap(
			SVDBArgFileIndexBuildData 		build_data,
			Map<Integer, SVDBFile>			map,
			ISVDBChildParent				scope,
			int								curr_id,
			SVDBFile						file) {
		
		for (ISVDBChildItem it : scope.getChildren()) {
			SVDBLocation l = it.getLocation();
			
			if (l != null && l.getFileId() != curr_id) {
				int new_id = l.getFileId();
				SVDBFile f = map.get(new_id);
				
				if (f == null) {
					f = new SVDBFile();
					map.put(new_id, f);
				}
		
				f.addChildItem(it);
				if (it instanceof ISVDBScopeItem) {
					createSubFileMap(build_data, map, (ISVDBChildParent)it, new_id, f);
				}
			} else {
				file.addChildItem(it);
			}
		}
		
	}

	/**
	 * Method performs the core work of locating the contents 
	 * of a file. 
	 * 
	 * Preconditions:
	 * - Index up-to-date
	 * - Only resolved paths passed in
	 * @param r_path
	 * @return
	 */
	private SVDBFile findFileInt(String r_path) {
		SVDBFile ret = null;
		SVDBFile root_file = findRootFile(fBuildData, r_path);
		
		if (root_file != null) {
			// Copy 
			int file_id = fBuildData.mapFilePathToId(r_path, false);
			ret = new SVDBFile(r_path);
		
			synchronized (fBuildData) {
				extractFileContents(ret, root_file, file_id);
			}
		}
		
		return ret;
	}
	
	// Search a specific path resolution
	private SVDBFile findRootFile(SVDBArgFileIndexBuildData build_data, String path) {
		SVDBFile ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
		
		synchronized (build_data) {
			// Search the file tree of each root file
			Map<String, List<String>> inc_map = build_data.fIndexCacheData.fRootIncludeMap;
			String root = null;
			for (Entry<String, List<String>> e : inc_map.entrySet()) {
				if (e.getKey().equals(path) || e.getValue().contains(path)) {
					root = e.getKey();
					break;
				}
			}
	
			if (root != null) {
				SVDBFileTree ft = build_data.fCache.getFileTree(
						new NullProgressMonitor(), root, false);
				ret = build_data.fCache.getFile(new NullProgressMonitor(), root);
			}
			
			/*
			for (String root_path : build_data.fCache.getFileList(false)) {
				SVDBFileTree ft = build_data.fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
				if (findTargetFileTree(ft, paths) != null) {
					ret = build_data.fCache.getFile(new NullProgressMonitor(), root_path);
					break;
				}
			}
			 */
		}
		
		return ret;
	}

	private SVDBFileTree findTargetFileTree(SVDBArgFileIndexBuildData build_data, String path) {
		SVDBFileTree ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
		
		synchronized (build_data) {
			Map<String, List<String>> inc_map = build_data.fIndexCacheData.fRootIncludeMap;
			String root = null;
			for (Entry<String, List<String>> e : inc_map.entrySet()) {
				if (e.getKey().equals(path) || e.getValue().contains(path)) {
					root = e.getKey();
					break;
				}
			}
			
			if (root != null) {
				SVDBFileTree ft = build_data.fCache.getFileTree(
						new NullProgressMonitor(), root, false);
				ret = findTargetFileTree(ft, paths);
			}
		
			/*
			// Search the file tree of each root file
			Set<String> file_list = build_data.fCache.getFileList(false);
//			System.out.println("file_list: " + file_list.size());
			for (String root_path : file_list) {
				long start = System.currentTimeMillis();
				SVDBFileTree ft = build_data.fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
//				System.out.println("Check: " + root_path + " " + ft + " " + paths);
				ret = findTargetFileTree(ft, paths);
				long end = System.currentTimeMillis();
				System.out.println("findTargetFileTree " + root_path + " " + (end-start) + "ms");
			
				if (ret != null) {
					break;
				}
			}
			 */
		}
		
		return ret;
	}

	/**
	 * Locate scopes to add to the target file
	 * 
	 * @param ret
	 * @param parent
	 * @param file_id
	 */
	private void extractFileContents(
			SVDBFile			ret,
			ISVDBChildParent	parent, 
			int 				file_id) {
		// indicates whether we've found the target
		// file at this scope level. We don't need to
		// traverse through any more sub-scopes once
		// we've found scopes in the target file
		boolean found_file = false;
		
		SVDBLocation l = parent.getLocation();
		
		if (fDebugEn) {
			fLog.debug("--> extractFileContents " + SVDBItem.getName(parent) + 
					" l.file_id=" + ((l != null)?l.getFileId():"null") + " " + file_id);
		}
	
		if (l != null && l.getFileId() == file_id) {
			ret.addChildItem(parent);
			found_file = true;
			if (fDebugEn) {
				fLog.debug("  -- foundFile(parent) ; add " + SVDBItem.getName(parent));
			}
		} else {
			for (ISVDBChildItem c : parent.getChildren()) {
				l = c.getLocation();
				if (l != null && l.getFileId() == file_id) {
					ret.addChildItem(c);
					found_file = true;
					if (fDebugEn) {
						fLog.debug("  -- foundFile ; add " + SVDBItem.getName(c));
					}
				} else if (c instanceof ISVDBChildParent) {
					if (!found_file) {
						extractFileContents(ret, (ISVDBChildParent)c, file_id);
					} else {
						/*
						if (fDebugEn) {
							fLog.debug("  -- stopping because " + SVDBItem.getName(c) + 
									" is a child parent ; l=" + l + " target_file=" + file_id);
						}
						 */
						// Not safe to stop, since we may have just recursed into a `included
						// file. TODO: May be able to optimize in the future
						
//						break;
					}
				}
			}
		}
		
		if (fDebugEn) {
			fLog.debug("<-- extractFileContents " + SVDBItem.getName(parent));
		}
	}
	
	private SVDBFileTree findTargetFileTree(SVDBFileTree ft, String paths[]) {
		SVDBFileTree ret = null;
				
		for (String path : paths) {
			if (path == null) {
				continue;
			}
			
			if (ft.getFilePath().equals(path)) {
				ret = ft;
				break;
			} else {
				for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
					if ((ret = findTargetFileTree(ft_s, paths)) != null) {
						break;
					}
				}
			}
			if (ret != null) {
				break;
			}
		}
		
		return ret;
	}

	private SVDBFileTree findTargetFileTree(SVDBFileTree ft, String path) {
		SVDBFileTree ret = null;
				
		if (ft.getFilePath().equals(path)) {
			ret = ft;
		} else {
			for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
				if ((ret = findTargetFileTree(ft_s, path)) != null) {
					break;
				}
			}
		}
		
		return ret;
	}

	private SVDBFileTree findRootFileTree(SVDBArgFileIndexBuildData build_data, String path) {
		SVDBFileTree ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
		
		synchronized (build_data) {
			String root = null;
			Map<String, List<String>> inc_map = build_data.fIndexCacheData.fRootIncludeMap;
			for (Entry<String, List<String>> e : inc_map.entrySet()) {
				if (e.getKey().equals(path) || e.getValue().contains(path)) {
					root = e.getKey();
					break;
				}
			}
			
			if (root != null) {
				ret = build_data.fCache.getFileTree(
						new NullProgressMonitor(), root, false);
			}
		}

		return ret;
	}
	
	@SuppressWarnings("unused")
	private SVDBFileTree findRootFileTree(SVDBFileTree parent, String paths[]) {
		for (String path : paths) {
			if (path == null) {
				continue;
			}
			
			if (parent.getFilePath().equals(path)) {
				return parent;
			} else {
				for (SVDBFileTree ft_s : parent.getIncludedFileTreeList()) {
					if (findRootFileTree(ft_s, paths) != null) {
						return parent;
					}
				}
			}
		}
		return null;
	}
	
	/**
	 * Implementation of ISVDBIndexIterator method
	 */
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String path) {
		// TODO: Update implementation
		String r_path = path;
		SVDBFile file = null;
		
		checkInIndexOp("findPreProcFile");

		SVDBFileTree ft = findTargetFileTree(fBuildData, r_path);
	
		if (ft != null) {
			file = ft.fSVDBFile;
		}

		return file;
	}
	
	
	public boolean doesIndexManagePath(String path) {
		checkInIndexOp("findPreProcFile");
		
		path = SVFileUtils.resolvePath(path, getBaseLocation(), 
				fFileSystemProvider, fInWorkspaceOk);
	
		List<String> srcfiles = fBuildData.fIndexCacheData.fSrcFileList;
		
		return (srcfiles != null && srcfiles.contains(path));
	}

	public List<SVDBMarker> getMarkers(String path) {
		if (fDebugEn) {
			fLog.debug("-> getMarkers: " + path);
		}
		
		checkInIndexOp("getMarkers");

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		// TODO: Doesn't consider that root file isn't necessarily what we're after
		boolean is_argfile = false;
		String r_path = path;
	
		synchronized (fBuildData) {
			is_argfile = fBuildData.fIndexCacheData.fArgFilePaths.contains(path);
		}
		
		if (is_argfile) {
			synchronized (fBuildData) {
//				SVDBFileTree ft = fCache.getFileTree(new NullProgressMonitor(), r_path, true);
//						ft.fMarkers);
				markers.addAll(fBuildData.fCache.getMarkers(r_path));
			}
		} else {
			findFileMarkersInt(markers, path);
		}
			
		if (fDebugEn) {
			fLog.debug("<- getMarkers: " + path + ": " + markers.size());
		}

		return markers;
	}

	/**
	 * Locates markers for the specified file and adds them to the list
	 * 
	 * @param markers
	 * @param r_path
	 */
	private void findFileMarkersInt(List<SVDBMarker> markers, String r_path) {
		List<SVDBMarker>	root_markers = null;
		int 				file_id = -1;
		SVDBFileTree 		target_ft = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fFileSystemProvider.resolvePath(r_path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			/*
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
			 */
		}
		
		synchronized (fBuildData) {
			String root_file = findRootFilePath(fBuildData, r_path);
			
			if (root_file != null) {
				SVDBFileTree ft = fBuildData.fCache.getFileTree(
						new NullProgressMonitor(), root_file, false);
				target_ft = findTargetFileTree(ft, r_path);
				file_id = fBuildData.mapFilePathToId(root_file, false);
				root_markers = fBuildData.fCache.getMarkers(root_file);
			}
			
			// Search the file tree of each root file
			/*
			for (String root_path : fBuildData.fCache.getFileList(false)) {
				SVDBFileTree ft = fBuildData.fCache.getFileTree(
						new NullProgressMonitor(), root_path, false);
				if ((target_ft = findTargetFileTree(ft, paths)) != null) {
					file_id = fBuildData.mapFilePathToId(root_path, false);
					root_markers = fBuildData.fCache.getMarkers(root_path);
					break;
				}
			}
			 */
			
			if (root_markers != null) {
				for (SVDBMarker m : root_markers) {
					if (m.getLocation() != null && m.getLocation().getFileId() == file_id) {
						markers.add(m);
					}
				}
			}
		
			if (target_ft != null && target_ft.fMarkers != null) {
				for (SVDBMarker m : target_ft.fMarkers) {
					markers.add(m);
				}
			}
		}
	}
	
	private String findRootFilePath(SVDBArgFileIndexBuildData build_data, String path) {
		String ret = null;
		
		synchronized (build_data) {
			Map<String, List<String>> root_map = build_data.fIndexCacheData.fRootIncludeMap;
			
			if (root_map.containsKey(path)) {
				ret = path;
			} else {
				for (Entry<String, List<String>> e : root_map.entrySet()) {
					if (e.getValue().contains(path)) {
						ret = e.getKey();
						break;
					}
				}
			}
		}
		
		return ret;
	}

	private void addFile(
			SVDBArgFileIndexBuildData 	build_data, 
			String 						path, 
			boolean 					is_argfile) {
		fLog.debug("addFile: " + path + " is_argfile=" + is_argfile);
		long last_modified = build_data.fFileSystemProvider.getLastModifiedTime(path);
		build_data.fCache.addFile(path, is_argfile);
		build_data.fCache.setLastModified(path, last_modified, is_argfile);
		
		if (!is_argfile) {
			build_data.fIndexCacheData.fRootFileList.add(path);
		}

		addFileDir(build_data, path);
	}

	private void addFileDir(SVDBArgFileIndexBuildData build_data, String file_path) {
		File f = new File(file_path);
		File p = f.getParentFile();

		if (p != null && !build_data.fFileDirs.contains(p.getPath())) {
			build_data.fFileDirs.add(p.getPath());
		}
	}

	public SVDBSearchResult<String> findIncludedFilePath(String path) {
		String file = null;

		String res_path = SVFileUtils.resolvePath(path, 
				getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);

		if (fFileSystemProvider.fileExists(res_path)) {
			return new SVDBSearchResult<String>(res_path, this);
		}
		
		for (String inc_dir : fBuildData.fIndexCacheData.getIncludePaths()) {
			String inc_path = SVFileUtils.resolvePath(inc_dir + "/" + path, 
					getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
			if (fFileSystemProvider.fileExists(inc_path)) {
				if (fDebugEn) {
					fLog.debug("findIncludedFilePath: located include \"" + path + "\"");
				}

				file = inc_path;
				break;
			}
			/*
			else {
				if (fDebugEn) {
					fLog.debug("findIncludedFile: file \"" + inc_path
							+ "\" does not exist");
				}
			}
			 */
		}

		if (file != null) {
			if (fDebugEn) {
				fLog.debug("findIncludedFile: Found and parsed new include file");
			}
			return new SVDBSearchResult<String>(file, this);
		}

		return null;
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider provider) {
		// TODO: Unused ISVDBIndex method
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {
		synchronized (fIndexChangeListeners) {
			fIndexChangeListeners.add(l);
		}
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		synchronized (fIndexChangeListeners) {
			fIndexChangeListeners.remove(l);
		}
	}

	public Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor 	monitor,
			InputStream 		in, 
			String 				path, 
			List<SVDBMarker> 	markers) {
		SVDBFile file=null, file_ft=null;
		
		synchronized (fBuildData) {
			String r_path = SVFileUtils.resolvePath(
					path, getResolvedBaseLocation(), 
					fFileSystemProvider, fInWorkspaceOk);

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
			// TODO: using 'this' as the include provider 
			// may not be ideal
			SVPreProcessor2 preproc = new SVPreProcessor2(
					r_path, in, fBuildData, fReadOnlyFileMapper);

			// TODO: add macros from FT
			List<SVDBMacroDef> incoming_macros = calculateIncomingMacros(fBuildData, r_path);
			end = System.currentTimeMillis();
				
			for (SVDBMacroDef m : incoming_macros) {
				preproc.setMacro(m);
			}

			fLog.debug("--> PreProcess " + r_path);
			start = System.currentTimeMillis();
			SVPreProcOutput out = preproc.preprocess();
			end = System.currentTimeMillis();
			fLog.debug("<-- PreProcess " + r_path + " " + (end-start) + "ms");

			ParserSVDBFileFactory f = new ParserSVDBFileFactory();
			f.setFileMapper(fReadOnlyFileMapper);

			fLog.debug("--> Parse " + r_path);
			SVLanguageLevel language_level = SVLanguageLevel.computeLanguageLevel(r_path);
			start = System.currentTimeMillis();
			file = f.parse(language_level, out, r_path, markers);
			end = System.currentTimeMillis();
			fLog.debug("<-- Parse " + r_path + " " + (end-start) + "ms");
			file_ft = null;
		}
		
		return new Tuple<SVDBFile, SVDBFile>(file_ft, file);
	}

	/**
	 * Traverse through the FileTree structure to calculate the
	 * macros defined prior to parse of a specific file. This
	 * method is only used by the parse() method used to parse
	 * content in the context of indexed content
	 * 
	 * @param ft
	 * @return
	 */
	private List<SVDBMacroDef> calculateIncomingMacros(
			SVDBArgFileIndexBuildData	build_data,
			String						path) {
		Map<String, SVDBMacroDef> all_defs = new HashMap<String, SVDBMacroDef>();
		List<SVDBMacroDef> defs = new ArrayList<SVDBMacroDef>();
		
		// First, collect the macros from the root 
		SVDBFileTree ft = findTargetFileTree(build_data, path);
		
		if (ft != null) {
			// Collect macros up the inclusion tree
			collectRootFileTreeMacros(all_defs, ft);
		}
		
		if (build_data.isMFCU()) {
			// Determine the index in the root files
			SVDBFileTree root_ft = findRootFileTree(build_data, path);
		
			List<String> root_files = build_data.getRootFileList();
			int root_idx = root_files.indexOf(root_ft.getFilePath());
			
			// Step back through the root files and add in macro state
			for (int i=root_idx-1; i>=0; i--) {
				String root_file_path = root_files.get(i);
				root_ft = findRootFileTree(build_data, root_file_path);
				for (int j=root_ft.getIncludedFileTreeList().size(); j>=0; j--) {
					SVDBFileTreeMacroList ml = root_ft.fMacroSetList.get(j);
					
					for (SVDBMacroDef m : ml.getMacroList()) {
						if (!all_defs.containsKey(m.getName())) {
							all_defs.put(m.getName(), m);
						}
					}
					
					if (j < root_ft.getIncludedFileTreeList().size()) {
						SVDBFileTree inc_ft = root_ft.getIncludedFileTreeList().get(j);
						collectRootFileTreeMacros(all_defs, root_ft);
					}
				}
			}
		}
		
		// Finally, add global defines
		for (Entry<String, String> e : build_data.getDefines().entrySet()) {
			if (!all_defs.containsKey(e.getKey())) {
				all_defs.put(e.getKey(), new SVDBMacroDef(e.getKey(), e.getValue()));
			}
		}
		
		for (Entry<String, String> e : build_data.getGlobalDefines().entrySet()) {
			if (!all_defs.containsKey(e.getKey())) {
				all_defs.put(e.getKey(), new SVDBMacroDef(e.getKey(), e.getValue()));
			}
		}
	
		// Finally, flatten out the macro list
		for (Entry<String, SVDBMacroDef> e : all_defs.entrySet()) {
			defs.add(e.getValue());
		}
		
		return defs;
	}

	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {

		return new SVDBIndexItemIterator(
				getFileList(new NullProgressMonitor()), this);
	}

	public SVDBFile findFile(String path) {
		return findFile(new NullProgressMonitor(), path);
	}

	public SVDBFile findPreProcFile(String path) {
		return findPreProcFile(new NullProgressMonitor(), path);
	}

	public SVDBFileTree findFileTree(
			String 		path,
			boolean 	is_argfile) {
		
		checkInIndexOp("findFileTree");

		SVDBFileTree ft = null;
		synchronized (fBuildData) {
			ft = fBuildData.fCache.getFileTree(
					new NullProgressMonitor(), path, is_argfile);
		}

		return ft;
	}

	public void dispose() {
		fLog.debug("dispose() - " + getBaseLocation());

		synchronized (fBuildData) {
			if (fBuildData.fCache != null) {
				fBuildData.fCache.sync();
			}
			if (fFileSystemProvider != null) {
				fFileSystemProvider.dispose();
			}
		}
	}

	/**
	 * getFileNames() -- implementation for IndexIterator
	 * @param monitor
	 * @return
	 */
	public Iterable<String> getFileNames(IProgressMonitor monitor) {
		return new Iterable<String>() {
			public Iterator<String> iterator() {
				List<String> ret = new ArrayList<String>();
				synchronized (fBuildData) {
					ret.addAll(fBuildData.fIndexCacheData.fSrcFileList);
				}
				return ret.iterator();
			}
		};
	}

	/**
	 * Add the global declarations from the specified scope to the declaration
	 * cache
	 * 
	 * @param filename
	 * @param scope
	 */
	private void cacheDeclarations(
			SVDBArgFileIndexBuildData	build_data,
			SVDBFile 					file, 
			SVDBFileTree 				ft) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = build_data.getDeclCacheMap();
		String file_path = ft.getFilePath();

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "cacheDeclarations: " + ft.getFilePath());
		}
		
		List<SVDBDeclCacheItem> file_item_list;
		
		if (!decl_cache.containsKey(file_path)) {
			file_item_list = new ArrayList<SVDBDeclCacheItem>();
			decl_cache.put(file_path, file_item_list);
		} else {
			file_item_list = decl_cache.get(file_path);
			file_item_list.clear();
		}

		Set<String> processed_files = new HashSet<String>();
		processed_files.add(file_path);
		
		int fileid = build_data.mapFilePathToId(file_path, false);

		cacheFileDeclarations(
				build_data,
				fileid, 
				file_item_list, 
				null, // pkg_item_list
				file,
				ft);
		/*
		cacheFileTreeDeclarations(
				ft,
				file_item_list);
		 */
				

		/** TODO: 
		SVDBFileTree ft = findFileTree(file.getFilePath(), false);
		if (ft != null) {
			cacheDeclarations(processed_files, file.getFilePath(),
					decl_cache.get(file.getFilePath()), null, null,
					ft.getSVDBFile(), true);
		}
		 */
	}

	private void cacheFileDeclarations(
			SVDBArgFileIndexBuildData		build_data,
			int								fileid,
			List<SVDBDeclCacheItem> 		decl_list,
			List<SVDBDeclCacheItem> 		pkg_decl_list,
			ISVDBChildParent 				scope,
			SVDBFileTree					ft) {
		int curr_fileid = fileid;
		String curr_filename = build_data.mapFileIdToPath(curr_fileid);
		
		if (fDebugEn) {
			fLog.debug("--> cacheFileDeclarations(file=" + curr_filename + ", " + scope);
		}

		for (ISVDBChildItem item : scope.getChildren()) {
			if (fDebugEn) {
				fLog.debug("  item: " + item.getType() + " "
						+ SVDBItem.getName(item));
			}
			
			if (item.getLocation() != null && 
					item.getLocation().getFileId() != curr_fileid &&
					item.getLocation().getFileId() > 0) {
				curr_fileid = item.getLocation().getFileId();
				curr_filename = build_data.mapFileIdToPath(curr_fileid);
			}
			
			if (item.getType().isElemOf(SVDBItemType.PackageDecl)) {
				SVDBPackageDecl pkg = (SVDBPackageDecl) item;
				List<SVDBDeclCacheItem> pkg_decl_l;

				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, curr_filename, pkg
							.getName(), item.getType(), false));
				}
				
				Map<String, List<SVDBDeclCacheItem>> pkg_map = 
						build_data.fIndexCacheData.getPackageCacheMap();

				if (pkg_map.containsKey(pkg.getName())) {
					pkg_decl_l = pkg_map.get(pkg.getName());
				} else {
					pkg_decl_l = new ArrayList<SVDBDeclCacheItem>();
					pkg_map.put(pkg.getName(), pkg_decl_l);
				}
				pkg_decl_l.clear();
				
				cacheFileDeclarations(build_data, curr_fileid, 
						decl_list, pkg_decl_l, pkg, ft);
				
				/* TODO: 
				SVDBPackageDecl pkg = (SVDBPackageDecl) item;

				// Now, proceed looking for explicitly-included content
				cacheDeclarations(processed_files, filename, decl_list,
						pkg.getName(), pkg_map.get(pkg.getName()), pkg, false);
				*/
			} else if (item.getType().isElemOf(SVDBItemType.Function,
					SVDBItemType.Task, SVDBItemType.ClassDecl,
					SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl,
					SVDBItemType.ProgramDecl)) {
				if (decl_list != null) {
					fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
							+ ((ISVDBNamedItem) item).getName() + " to cache");
					decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							false));
				}
				if (pkg_decl_list != null) {
					fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
							+ ((ISVDBNamedItem) item).getName() + " to pkg_decl cache");
					pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							false));
				}
				if (item.getType().isElemOf(SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl)) {
					cacheFileDeclarations(build_data, curr_fileid, 
						decl_list, null, (ISVDBScopeItem)item, ft);
				}
			} else if (item.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt decl = (SVDBVarDeclStmt) item;

				for (ISVDBChildItem ci : decl.getChildren()) {
					SVDBVarDeclItem di = (SVDBVarDeclItem) ci;
					fLog.debug(LEVEL_MID,
							"Adding var declaration: " + di.getName());

					if (decl_list != null) {
						decl_list.add(new SVDBDeclCacheItem(this, curr_filename, 
								di.getName(), SVDBItemType.VarDeclItem, false));
					}
					if (pkg_decl_list != null) {
						pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename, 
								di.getName(), SVDBItemType.VarDeclItem, false));
					}
				}
			} else if (item.getType() == SVDBItemType.TypedefStmt) {
				// Add entries for the typedef
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(), false));
				}
				
				if (pkg_decl_list != null) {
					pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(), false));
				}

				SVDBTypedefStmt td = (SVDBTypedefStmt) item;
				if (td.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					// Add entries for all enumerators
					SVDBTypeInfoEnum e = (SVDBTypeInfoEnum) td.getTypeInfo();
					fLog.debug("Adding enum " + e.getName() + " to cache");
					for (SVDBTypeInfoEnumerator en : e.getEnumerators()) {
						fLog.debug("Adding enumerator " + en.getName()
								+ " to cache");
						if (decl_list != null) {
							decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
									((ISVDBNamedItem) en).getName(), 
									en.getType(), false));
						}
						if (pkg_decl_list != null) {
							pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
									((ISVDBNamedItem) en).getName(), 
									en.getType(), false));
						}
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- cacheFileDeclarations(" + curr_filename + ", " + scope);
		}
	}
	
	@SuppressWarnings("unused")
	private void cacheFileTreeDeclarations(
			SVDBFileTree				ft,
			List<SVDBDeclCacheItem>		file_item_list) {
		
		SVDBFile file = ft.getSVDBFile();
		
		for (ISVDBChildItem c : file.getChildren()) {
			
			
		}

		for (SVDBFileTree ft_s : ft.getIncludedFileTreeList()) {
			cacheFileTreeDeclarations(ft_s, file_item_list);
		}
	}

	/*
	private void cacheReferences(SVDBFile file) {
		SVDBFileRefCollector collector = new SVDBFileRefCollector();
		collector.visitFile(file);

		Map<String, SVDBRefCacheEntry> ref_map = getCacheData()
				.getReferenceCacheMap();
		if (ref_map.containsKey(file.getFilePath())) {
			ref_map.remove(file.getFilePath());
		}
		SVDBRefCacheEntry ref = collector.getReferences();
		ref.setFilename(file.getFilePath());
		ref_map.put(file.getFilePath(), ref);
	}
	 */

	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor,
			SVDBDeclCacheItem pkg_item) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		Map<String, List<SVDBDeclCacheItem>> pkg_cache = 
				fBuildData.fIndexCacheData.getPackageCacheMap();

		checkInIndexOp("findPackageDecl");

		List<SVDBDeclCacheItem> pkg_content = pkg_cache.get(pkg_item.getName());

		if (pkg_content != null) {
			ret.addAll(pkg_content);
		}

		return ret;
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor 		monitor, 
			String 					name, 
			ISVDBFindNameMatcher 	matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		
		checkInIndexOp("findGlobalScopeDecl");
		
		Map<String, List<SVDBDeclCacheItem>> decl_cache = 
				fBuildData.fIndexCacheData.getDeclCacheMap();

		for (Entry<String, List<SVDBDeclCacheItem>> e : decl_cache.entrySet()) {
			for (SVDBDeclCacheItem item : e.getValue()) {
				if (matcher.match(item, name)) {
					ret.add(item);
				}
			}
		}

		return ret;
	}

	public List<SVDBRefCacheItem> findReferences(IProgressMonitor monitor,
			String name, ISVDBRefMatcher matcher) {
		List<SVDBRefCacheItem> ret = new ArrayList<SVDBRefCacheItem>();

		checkInIndexOp("findReferences");

		Map<String, SVDBRefCacheEntry> ref_cache = 
				fBuildData.fIndexCacheData.getReferenceCacheMap();
		for (Entry<String, SVDBRefCacheEntry> e : ref_cache.entrySet()) {
			matcher.find_matches(ret, e.getValue(), name);
		}

		for (SVDBRefCacheItem item : ret) {
			item.setRefFinder(this);
		}

		return ret;
	}

	public List<SVDBRefItem> findReferences(
			IProgressMonitor 		monitor,
			SVDBRefCacheItem 		item) {
		checkInIndexOp("findReferences");

		SVDBRefFinder finder = new SVDBRefFinder(item.getRefType(),
				item.getRefName());

		SVDBFile file = findFile(item.getFilename());

		return finder.find_refs(file);
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		
		checkInIndexOp("getDeclFile");

		SVDBFile file = null;

		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findFileTree(item.getFilename(), false);
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

	// FIXME:
	public SVDBFile getDeclFilePP(
			IProgressMonitor 		monitor,
			SVDBDeclCacheItem 		item) {
		checkInIndexOp("getDeclFilePP");

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

	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}

	private void discoverRootFiles(
			IProgressMonitor 			monitor,
			SVDBArgFileIndexBuildData	build_data) {
		fLog.debug("discoverRootFiles - " + getBaseLocation());

		/*
		clearFilesList();
		clearIncludePaths();
		clearDefines();
		 */

		monitor.beginTask("Discover Root Files", 4);

		// Add an include path for the arg file location
		build_data.addIncludePath(getResolvedBaseLocationDir());

		String resolved_argfile_path = getResolvedBaseLocation();
		if (getFileSystemProvider().fileExists(resolved_argfile_path)) {
			processArgFile(
					new SubProgressMonitor(monitor, 4), 
					build_data,
					null, 
					null, 
					getResolvedBaseLocationDir(),
					getResolvedBaseLocation(), 
					false);
		} else {
			String msg = "Argument file \"" + getBaseLocation() + "\" (\""
					+ getResolvedBaseLocation() + "\") does not exist";
			fLog.error(msg);
			if (getProject() != null) {
				// TODO: must save this somewhere...
				getFileSystemProvider().addMarker(
						"${workspace_loc}/" + getProject(),
						ISVDBFileSystemProvider.MARKER_TYPE_ERROR, 0, msg);
			}
		}

		monitor.done();
	}

	private SVDBFile parseArgFile(
			SVDBArgFileIndexBuildData	build_data,
			String						path,
			String						base_location_dir,
			Set<String>					processed_paths,
			List<SVDBMarker>			markers) {
		SVDBFile ret = new SVDBFile(path);
		InputStream in = null;
		
		String resolved_path = SVFileUtils.resolvePath(
				path, base_location_dir, getFileSystemProvider(), true);
	
		if (processed_paths.contains(resolved_path)) {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"Recursive inclusion of file \"" + path + "\" (" + resolved_path + ")"));
		} else if ((in = getFileSystemProvider().openStream(resolved_path)) != null) {
			long last_modified = getFileSystemProvider().getLastModifiedTime(resolved_path);
			processed_paths.add(resolved_path);
			ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(getProjectHndl());
			SVArgFilePreProcessor pp = new SVArgFilePreProcessor(
					in, resolved_path, vp);
			
			SVArgFilePreProcOutput pp_out = pp.preprocess();
			
			SVArgFileLexer lexer = new SVArgFileLexer();
			lexer.init(null, pp_out);
			
			SVArgFileParser parser = new SVArgFileParser(
					base_location_dir, base_location_dir,
					getFileSystemProvider());
			parser.init(lexer, path);
		
			try {
				parser.parse(ret, markers);
			} catch (SVParseException e) {}

			
			processed_paths.add(resolved_path);
			
			if (fDebugEn) {
				fLog.debug("File: " + resolved_path + " has " + markers.size() + " errors");
				for (SVDBMarker m : markers) {
					fLog.debug("  " + m.getMessage());
				}
			}
			build_data.fCache.setMarkers(resolved_path, markers, true);
			build_data.fCache.setFile(resolved_path, ret, true);
			build_data.fCache.setLastModified(resolved_path, last_modified, true);

			if (fDebugEn) {
				fLog.debug("File(cached): " + resolved_path + " has " + 
						build_data.fCache.getMarkers(resolved_path).size() + " errors");
			}
		} else {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"File \"" + path + "\" (" + resolved_path + ") does not exist"));
		}

		return ret;
	}	

	private void processArgFile(
			IProgressMonitor				monitor, 
			SVDBArgFileIndexBuildData		build_data,
			SVDBFileTree					parent,
			Set<String> 					processed_paths, 
			String							base_location_dir,
			String 							path,
			boolean							is_root) {
		path = SVFileUtils.normalize(path);

		if (processed_paths == null) {
			processed_paths = new HashSet<String>();
		}
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		SVDBFileTree ft = new SVDBFileTree(path);
		ft.setIncludeRoot((is_root || parent == null));
		
		String sub_base_location_dir = base_location_dir;
		
		if (is_root) {
			sub_base_location_dir = SVFileUtils.getPathParent(path);
		}
		
		// parse the argument file 
		SVDBFile argfile = parseArgFile(build_data, path, 
				sub_base_location_dir, processed_paths, markers);
		
		if (parent != null) {
			ft.addIncludedByFile(parent.getFilePath());
			parent.addIncludedFile(path);
		}

		long last_modified = fFileSystemProvider.getLastModifiedTime(path);
		build_data.fCache.setFile(path, argfile, true);
		build_data.fCache.setLastModified(path, last_modified, true);
	
		build_data.addArgFilePath(path);
		
		if (argfile != null) {
			build_data.addArgFile(argfile);

			for (ISVDBChildItem ci : argfile.getChildren()) {
				if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
					// Process the included file
					SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
					String sub_path = SVFileUtils.resolvePath(stmt.getPath(), sub_base_location_dir, fFileSystemProvider, fInWorkspaceOk);
					
					// TODO: handle monitor
					if (getFileSystemProvider().fileExists(sub_path)) {
						if (!processed_paths.contains(sub_path)) {
							processArgFile(new NullProgressMonitor(), build_data,
									ft, processed_paths, sub_base_location_dir, 
									sub_path, stmt.isRootInclude());
						} else {
							SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
									"Recursive inclusion of file \"" + path + "\" (" + sub_path + ")");
							m.setLocation(stmt.getLocation());
							markers.add(m);
						}
					} else {
						/** 
						SVDBMarker m = new SVDBMarker(
								MarkerType.Error, MarkerKind.MissingInclude, 
								"Path \"" + sub_path + "\" does not exist");
						m.setLocation(stmt.getLocation());
						markers.add(m);
						 */
					}
				} else if (ci.getType() == SVDBItemType.ArgFileIncDirStmt) {
					SVDBArgFileIncDirStmt stmt = (SVDBArgFileIncDirStmt)ci;
					build_data.addIncludePath(stmt.getIncludePath());
				} else if (ci.getType() == SVDBItemType.ArgFileDefineStmt) {
					SVDBArgFileDefineStmt stmt = (SVDBArgFileDefineStmt)ci;
					build_data.addDefine(stmt.getKey(), stmt.getValue());
				} else if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
					SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt)ci;
					String res_f = SVFileUtils.resolvePath(stmt.getPath(), sub_base_location_dir, fFileSystemProvider, fInWorkspaceOk);

					if (getFileSystemProvider().fileExists(res_f)) {
						addFile(build_data, res_f, false);
					}
				} else if (ci.getType() == SVDBItemType.ArgFileMfcuStmt) {
					build_data.setMFCU();
				} else if (ci.getType() == SVDBItemType.ArgFileSrcLibPathStmt) {
					SVDBArgFileSrcLibPathStmt stmt = (SVDBArgFileSrcLibPathStmt)ci;
					
					if (getFileSystemProvider().isDir(stmt.getSrcLibPath())) {
						List<String> paths = getFileSystemProvider().getFiles(stmt.getSrcLibPath());
						Set<String> exts = SVFScanner.getSrcExts();
						for (String file_p : paths) {
							int last_dot = file_p.lastIndexOf('.');
							if (last_dot != -1) {
								String ext = file_p.substring(last_dot);
								if (exts.contains(ext)) {
									addFile(build_data, file_p, false);
								}
							}
						}
					} else {
						SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
								"Library Path directory \"" + stmt.getSrcLibPath() + "\" does not exist");
						m.setLocation(stmt.getLocation());
						markers.add(m);
					}
				}
			}

			// Save the markers, which might have been updated
			build_data.fCache.setMarkers(path, markers, true);
			build_data.fCache.setFileTree(path, ft, true);

			// Propagate markers to filesystem
// TODO:			propagateMarkers(path);
		} else {
			// Problem with root argument file
			// TODO: propagate markers
		}
	}
	
	
	private Map<String, SVDBMacroDef> parseFile(
			String 						path, 
			SVDBArgFileIndexBuildData 	build_data,
			Map<String, SVDBMacroDef>	defines) {
		long start, end;
		ParserSVDBFileFactory f = new ParserSVDBFileFactory();
		f.setFileMapper(build_data);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		InputStream in = fFileSystemProvider.openStream(path);

		start = System.currentTimeMillis();
		
		// Propagate defines to the pre-processor
		SVPreProcessor2 pp = new SVPreProcessor2(path, in, build_data, build_data);

		// Pass in defines
		for (Entry<String, SVDBMacroDef> def : defines.entrySet()) {
			pp.setMacro(def.getValue());
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> PreProcess " + path);
		}
		SVPreProcOutput pp_out = pp.preprocess();
		end = System.currentTimeMillis();
		
//		System.out.println("Pre-process " + path + " " + (end-start));
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "<-- PreProcess " + path + ": " +
					(end-start) + "ms");
		}
		
		SVDBFileTree ft = pp_out.getFileTree();
		
		// Add a mapping between root file and included files
		List<String> included_files = new ArrayList<String>();
		collectIncludedFiles(included_files, ft);
		build_data.fIndexCacheData.fRootIncludeMap.remove(path);
		build_data.fIndexCacheData.fRootIncludeMap.put(path, included_files);

		start = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> Parse " + path);
		}
		SVLanguageLevel language_level = SVLanguageLevel.computeLanguageLevel(path);
		SVDBFile file = f.parse(language_level, pp_out, path, markers);
		end = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "<-- Parse " + path + ": " +
					(end-start) + "ms");
		}
//		System.out.println("Parse " + path + " " + (end-start));

		start = System.currentTimeMillis();
		cacheDeclarations(build_data, file, ft);
		end = System.currentTimeMillis();
//		System.out.println("CacheDecl " + path + " " + (end-start));
		
		start = System.currentTimeMillis();
		long last_modified = fFileSystemProvider.getLastModifiedTime(path);
		build_data.fCache.setFile(path, file, false);
		build_data.fCache.setFileTree(path, ft, false);
		build_data.fCache.setMarkers(path, markers, false);
		build_data.fCache.setLastModified(path, last_modified, false);

		end = System.currentTimeMillis();
//		System.out.println("SetCache " + path + " " + (end-start));a

		if (build_data.isMFCU()) {
			// In MFCU mode, collect the defined macros and 
			// return them
			Map<String, SVDBMacroDef> defined_macros = new HashMap<String, SVDBMacroDef>();
			collectFileTreeMacros(defined_macros, ft);
			
			return defined_macros;
		} else {
			return null;
		}
	}

	/**
	 * Collects the macros defined by files in the containing
	 * root file prior to inclusion of this file. 
	 * 
	 * This method is used only by the parse() method
	 * 
	 * @param defines
	 * @param ft
	 */
	private void collectRootFileTreeMacros(
			Map<String, SVDBMacroDef> 		defines, 
			SVDBFileTree					ft) {
	
		while (ft.getParent() != null) {
			// Find the index where this file is included
			int include_idx = -1;
			
			SVDBFileTree p_ft = ft.getParent();
			for (int i=0; i<p_ft.getIncludedFileTreeList().size(); i++) {
				SVDBFileTree ft_i = p_ft.getIncludedFileTreeList().get(i);
				if (ft_i == ft) {
					include_idx = i;
					break;
				}
			}
			
			if (include_idx == -1) {
				break;
			}
			
			for (int i=include_idx; i>=0; i--) {
				// Collect the macros from defined at this level
				SVDBFileTree ft_i = p_ft.getIncludedFileTreeList().get(i);
				SVDBFileTreeMacroList ml = p_ft.fMacroSetList.get(i);
				
				for (SVDBMacroDef m : ml.getMacroList()) {
					if (!defines.containsKey(m.getName())) {
						defines.put(m.getName(), m);
					}
				}

				// Collect the macros defined by files included
				// in this file tree
			
				if (i < include_idx) {
					collectFileTreeMacros(defines, ft_i);
				}
			}
		
			// Move up a level
			ft = p_ft;
		}
	}
	
	/**
	 * Collect macros defined by files included in the specified file tree
	 * 
	 * @param defines
	 * @param ft
	 */
	private void collectFileTreeMacros(Map<String, SVDBMacroDef> defines, SVDBFileTree ft) {

		for (int i=ft.fIncludedFileTrees.size(); i>=0; i--) {
			SVDBFileTreeMacroList ml = ft.fMacroSetList.get(i);
			
			for (SVDBMacroDef m : ml.getMacroList()) {
				if (!defines.containsKey(m.getName())) {
					defines.put(m.getName(), m);
				}
			}
			
			if (i < ft.fIncludedFileTrees.size()) {
				SVDBFileTree ft_i = ft.fIncludedFileTrees.get(i);
				// Now, recurse and collect from included file trees
				collectFileTreeMacros(defines, ft_i);
			}
		}
	}
	
	private void collectIncludedFiles(List<String> included_files, SVDBFileTree ft) {
		for (SVDBFileTree ft_i : ft.getIncludedFileTreeList()) {
			if (!included_files.contains(ft_i.getFilePath())) {
				included_files.add(ft_i.getFilePath());
				collectIncludedFiles(included_files, ft_i);
			}
		}
	}

	/**
	 * Build all the files in the index
	 * 
	 * @param monitor
	 * @param build_data
	 */
	private void buildIndex(
			IProgressMonitor 				monitor,
			SVDBArgFileIndexBuildData		build_data) {
		long start_time=-1, end_time=-1;
		int total_work = 10000;
		int per_file_work = 0;
		
		monitor.beginTask("Build Index", total_work);

		// First, parse the argument files
		if (fDebugEn) {
			start_time = System.currentTimeMillis();
		}
		discoverRootFiles(new SubProgressMonitor(monitor, 100), build_data);
		if (fDebugEn) {
			end_time = System.currentTimeMillis();
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse argument files -- " + (end_time - start_time)
					+ "ms");
		}

		if (monitor.isCanceled()) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation() + " cancelled");
			return;
		}

		// Next, parse each of the discovered file paths
		List<String> paths = build_data.fIndexCacheData.fRootFileList;
		Map<String, SVDBMacroDef> defines = new HashMap<String, SVDBMacroDef>();

		if (fDebugEn) {
			start_time = System.currentTimeMillis();
		}
	
		if (paths.size() > 0) {
			per_file_work = (total_work / paths.size());
		}
		if (per_file_work == 0) {
			per_file_work = 1;
		}
	
		// Setup global definitions
		for (Entry<String, String> e : build_data.getGlobalDefines().entrySet()) {
			String key = e.getKey();
			String val = (e.getValue() != null)?e.getValue():"";
			if (defines.containsKey(key)) {
				defines.remove(key);
			}
			defines.put(key, new SVDBMacroDef(key, val));
		}

		for (Entry<String, String> e : build_data.getDefines().entrySet()) {
			String key = e.getKey();
			String val = (e.getValue() != null)?e.getValue():"";
			if (defines.containsKey(key)) {
				defines.remove(key);
			}
			defines.put(key, new SVDBMacroDef(key, val));
		}		
		
		for (int i=0; i<paths.size(); i++) {
			String path = paths.get(i);
			
			if (fDebugEn) {
				fLog.debug(LEVEL_MID, "Path: " + path);
			}
			
			if (fFileSystemProvider.fileExists(path)) {
				monitor.subTask("Parse " + path);
				
				Map<String, SVDBMacroDef> new_defines = parseFile(path, build_data, defines);
				
				if (monitor.isCanceled()) {
					fLog.debug(LEVEL_MIN, "Index " + getBaseLocation() + " cancelled");
					return;
				}
				
				if (build_data.isMFCU()) {
					// Accumulate the new defines
					for (Entry<String, SVDBMacroDef> e : defines.entrySet()) {
						if (!new_defines.containsKey(e.getKey())) {
							new_defines.put(e.getKey(), e.getValue());
						}
					}
					defines = new_defines;
				}

				monitor.worked(per_file_work);
			}
		}
		
		if (fDebugEn) {
			end_time = System.currentTimeMillis();
		}
	
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse source files -- " + (end_time - start_time)
					+ "ms");
		}
		
		monitor.done();
	}

	public ISVPreProcessor createPreProcScanner(String path) {
		SVPreProcessor2 ret = null;
		
		checkInIndexOp("createPreProcScanner");
		SVDBFileTree ft = findTargetFileTree(fBuildData, path);
		
//		System.out.println("ft=" + ft);
		
		if (ft != null) {
			List<SVDBFileTree> ft_l = new ArrayList<SVDBFileTree>();
		
			InputStream in = fFileSystemProvider.openStream(path);
			ret = new SVPreProcessor2(ft.getFilePath(), in, null, null);
			
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
		}

		return ret;
	}

	public String getFileFromId(int fileid) {
		return fBuildData.mapFileIdToPath(fileid);
	}

	private ISVPreProcFileMapper fReadOnlyFileMapper = new ISVPreProcFileMapper() {
		
		public int mapFilePathToId(String path, boolean add) {
			return SVDBArgFileIndex2.this.fBuildData.mapFilePathToId(path, false);
		}
		
		public String mapFileIdToPath(int id) {
			return SVDBArgFileIndex2.this.fBuildData.mapFileIdToPath(id);
		}
	};

	/**
	 * Implement of ISVDBIndexOperationRunner
	 */

	public void execOp(
			IProgressMonitor 		monitor, 
			ISVDBIndexOperation 	op,
			boolean					sync) {
		monitor.beginTask("", 1000);
		
		if (sync) {
			ensureIndexUpToDate(new SubProgressMonitor(monitor, 500));
		}

		// Ensure no other 
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
}
