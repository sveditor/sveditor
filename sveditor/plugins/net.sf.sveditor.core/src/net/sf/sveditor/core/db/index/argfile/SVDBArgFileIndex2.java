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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBArgFile;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
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
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.index.SVDBFindIncFileUtils;
import net.sf.sveditor.core.db.index.SVDBIncFileInfo;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBIndexFactoryUtils;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexStats;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexBuildJob;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles.FileListType;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRefresh;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache.FileType;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec;
import net.sf.sveditor.core.db.refs.ISVDBRefSearchSpec.NameMatchType;
import net.sf.sveditor.core.db.refs.ISVDBRefVisitor;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
import net.sf.sveditor.core.db.refs.SVDBFileRefFinder;
import net.sf.sveditor.core.db.refs.SVDBRefMatcher;
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
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.preproc.SVStringPreProcessor;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBArgFileIndex2 implements 
		ISVDBIndex, ISVDBIndexInt,  
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
	private boolean								fIndexRefreshed;
	private boolean								fIndexValid;
	private boolean 							fAutoRebuildEn;
	private boolean 							fIsDirty;
	
	private ISVDBIndexBuilder					fIndexBuilder;
	private int									fInIndexOp;
	
	private SVDBArgFileParser					fArgFileParser;
	
	
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
		
		fArgFileParser = new SVDBArgFileParser(
				getFileSystemProvider(),
				getBaseLocation(),
				getResolvedBaseLocation(),
				getResolvedBaseLocationDir(),
				getProjectHndl());
	}
	
	public void setIndexBuilder(ISVDBIndexBuilder builder) {
		fIndexBuilder = builder;
	}

	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		ISVDBIndexChangePlan plan = new SVDBIndexChangePlan(this, SVDBIndexChangePlanType.Empty);
		
		
		if (changes == null || !fIndexValid) {
			if (!fIndexValid) {
				// Return a 'build me' plan, since we're not valid
				plan = new SVDBIndexChangePlanRebuild(this);
			}
		} else {
			if (fDebugEn) {
				fLog.debug("--> createIndexChangePlan (incremental)");
			}
			synchronized (fBuildData) {
				List<String> changed_sv_files = new ArrayList<String>();
				List<String> changed_f_files = new ArrayList<String>();
				
				SVDBIndexChangePlanRebuildFiles rebuild_sv_files_plan = new SVDBIndexChangePlanRebuildFiles(this);
				SVDBIndexChangePlanRebuildFiles rebuild_arg_files_plan = new SVDBIndexChangePlanRebuildFiles(this);
				
				for (SVDBIndexResourceChangeEvent ev : changes) {
					String path = SVFileUtils.resolvePath(ev.getPath(), getResolvedBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
					if (fDebugEn) {
						fLog.debug("Changed file: " + path);
					}
					if (fBuildData.fIndexCacheData.containsFile(path, FILE_ATTR_SRC_FILE)) {
						if (fDebugEn) {
							fLog.debug("  Is a Source File");
						}
						if (!changed_sv_files.contains(path)) {
							changed_sv_files.add(path);
						}
					} else if (fBuildData.fIndexCacheData.containsFile(path, FILE_ATTR_ARG_FILE)) {
						if (fDebugEn) {
							fLog.debug("  Is an argument file");
						}
						// Argument file changed, so rebuild project
						if (!changed_f_files.contains(path)) {
							changed_f_files.add(path);
						}
						break;
					}
				}
				
				if (fDebugEn) {
					fLog.debug("  changed_sv_files: " + changed_sv_files.size() + 
							" changed_f_files: " + changed_f_files.size());
				}
				
				if (changed_sv_files.size() > 0) {
					if (changed_f_files.size() > 0) {
						// TODO: Both SV and argument files changed
						plan = create_incr_hybrid_plan(changed_sv_files, changed_f_files);
					} else {
						plan = create_incr_plan(changed_sv_files);
					}
				} else if (changed_f_files.size() > 0) {
					plan = create_incr_argfile_plan(changed_f_files);
				}
			
				/*
				if (changed_f_files.size() > 0) {
					// TODO: Full build for now
					plan = new SVDBIndexChangePlanRebuild(this);
				} else if (changed_sv_files.size() > 0) {
					plan = create_incr_plan(changed_sv_files);
				}
				 */
			}
			if (fDebugEn) {
				fLog.debug("<-- createIndexChangePlan (incremental)");
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
			/** MSB:
			if (fBuildData.fIndexCacheData.getReferenceCacheMap() != null) {
				for (Entry<String, SVDBRefCacheEntry> e : 
					fBuildData.fIndexCacheData.getReferenceCacheMap().entrySet()) {
					e.getValue().setFilename(e.getKey());
				}
			}
			 */

			// Register all files with the directory set
			for (String f : fBuildData.fCache.getFileList(false)) {
				fBuildData.addFileDir(f);
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
		
		fIndexRefreshed = true;
	}
	
	protected void rebuild_index(IProgressMonitor monitor) {
		long start = System.currentTimeMillis();
		
//		if (!fIndexRefreshed) {
//			refresh_index(new NullProgressMonitor());
//		}
		
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
		
		if (fDebugEn) {
			// Show the index stats
			fLog.debug(LEVEL_MIN, "Index Stats " + getBaseLocation() + ":\n" + 
					build_data.fIndexStats.toString());
		}
		
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
		
		long end = System.currentTimeMillis();
	
		monitor.done();
	}

	/**
	 * Rebuild 
	 * @param monitor
	 * @param plan
	 */
	private void rebuild_files(IProgressMonitor monitor, SVDBIndexChangePlanRebuildFiles plan) {
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "rebuild_files: " + plan.getFileListType());
		}
		
		monitor.beginTask("Update " + getBaseLocation(), 2*1000*plan.getFileList().size());
	
		ISVDBIndexCache cache = fCacheMgr.createIndexCache(getProject(), getBaseLocation());
		SVDBArgFileIndexBuildData build_data = new SVDBArgFileIndexBuildData(cache, getBaseLocation());
		SVDBLinkedArgFileIndexBuildData build_data_l = new SVDBLinkedArgFileIndexBuildData(
				build_data, fBuildData);
		build_data.fFileSystemProvider = fFileSystemProvider;
		
		synchronized (fBuildData) {
			// Must initialize the file mapper state so any
			// new files are given correct numberings
			build_data.initFileMapperState(fBuildData);
		}
	
		// Save the number of files pre, so we can update post
//		int n_files_pre = build_data.fIndexCacheData.getFileCount(FILE_ATTR_SRC_FILE);
		
		// First build a complete source list of files
		List<String> file_list = new ArrayList<String>();
		List<String> existing_files = new ArrayList<String>();
		List<String> added_files = new ArrayList<String>();
		
		if (plan.getFileListType() == FileListType.Source) {
			// simple: already have it
			file_list.addAll(plan.getFileList());
		} else if (plan.getFileListType() == FileListType.Filelist) {
			NullProgressMonitor m = new NullProgressMonitor();
			System.out.println("Plan: FileList");
			for (String f_file : plan.getFileList()) {
				synchronized (fBuildData) {
				SVDBFile argfile = fBuildData.getFile(m, f_file);
				System.out.println("file: " + f_file + " argfile=" + argfile);
				if (argfile != null) {
					fArgFileParser.collectSourceFiles(fBuildData, 
							(SVDBArgFile)argfile, existing_files);
				}
				}
			}
			System.out.println("Source Files: " + existing_files.size());
		
			// Process the new versions of the argument files
			Set<String> processed_paths = new HashSet<String>();
			for (String f_file : plan.getFileList()) {
				SVDBArgFile argfile = null;
				synchronized (fBuildData) {
					argfile = (SVDBArgFile)fBuildData.getFile(m, f_file);
				}
				
				fArgFileParser.processArgFile(monitor, build_data, null, processed_paths, 
						(argfile != null)?argfile.getBaseLocation():fBaseLocation,
						f_file, false);
			}
		
			// Collect the new source files to parse
			for (String f_file : plan.getFileList()) {
				synchronized (fBuildData) {
					SVDBFile argfile = build_data.getFile(m, f_file);
					System.out.println("file: " + f_file + " argfile=" + argfile);
					if (argfile != null) {
						fArgFileParser.collectSourceFiles(build_data, 
								(SVDBArgFile)argfile, file_list);
					}
				}
			}
		
			System.out.println("New Files: ");
			for (String path : file_list) {
				System.out.println("    Path: " + path);
			}
		} else if (plan.getFileListType() == FileListType.Hybrid) {
			// Both filelists and files changed
			
		}
		
		if (fDebugEn) {
			fLog.debug("Source files to parse: " + file_list.size());
			for (String path : file_list) {
				fLog.debug("  " + path);
			}
		}
	
		try {
			// TODO: order files based on previous processing order
			// Note: only important for MFCU mode

			// TODO: determine whether these are SV are .f files?
			for (String path : file_list) {
				monitor.subTask("Parse " + path);
				// path is a 'root' file
				InputStream in = fFileSystemProvider.openStream(path);
//				System.out.println("Remove: " + path + " from existing files");
				if (!existing_files.remove(path)) { // Remove the new path from the set of pre-existing ones
					added_files.add(path);
				} 
				
				if (in == null) {
					continue;
				}
				
				SVPreProcessor2 preproc = new SVPreProcessor2(
						path, in, build_data, build_data);

				fFileSystemProvider.closeStream(in);
				
				
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
				
				SVParser f = new SVParser();
				f.setFileMapper(build_data);
				
				SVLanguageLevel language_level;
				
				if (build_data.getForceSV()) {
					language_level = SVLanguageLevel.SystemVerilog;
				} else {
					language_level = SVLanguageLevel.computeLanguageLevel(path);
				}
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
				
				// Register any new files
				fLog.debug("fBuildData.NumSrcFiles=" + fBuildData.getNumSrcFiles() + " build_data.NumSrcFiles=" + 
						build_data.getNumSrcFiles());
				for (int i=fBuildData.getNumSrcFiles()+1; i<=build_data.getNumSrcFiles(); i++) {
					String path = build_data.mapFileIdToPath(i);
					int new_id = fBuildData.mapFilePathToId(path, true);
					fLog.debug("Add new src file: " + path + " id=" + new_id);
				}
			
				for (String path : file_list) {
					monitor.subTask("Merge " + path);
					SVDBFileTree     ft      = cache.getFileTree(new NullProgressMonitor(), path, false);
					SVDBFile         file    = cache.getFile(new NullProgressMonitor(), path);
					List<SVDBMarker> markers = cache.getMarkers(path);
				
					if (file != null) {
						fBuildData.fCache.setFile(path, file, false);
					} else {
						System.out.println("[ERROR] file " + path + " is null");
						try {
							throw new Exception();
						} catch (Exception e) {
							e.printStackTrace();
						}
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
				for (String path : added_files) {
					int attr = build_data.fIndexCacheData.getFileAttr(path);
					fBuildData.fIndexCacheData.addFile(path, attr);
				}
			
				// TODO: collect declaration info from these files and remove
				// from the declaration cache
				for (String path : existing_files) {
					System.out.println("Remove: " + path);
					fBuildData.removeFile(path, false);
					SVDBFile file = fBuildData.getFile(new NullProgressMonitor(), path);
					System.out.println("  Post-remove: " + file);
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
	
	private void discover_add_sourcefiles(
			SVDBArgFileIndexBuildData		build_data,
			String							base_location,
			Set<String> 					processed_argfiles,
			List<String> 					file_list, 
			String 							argfile) {
	

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
	
		plan.setFileListType(FileListType.Source);
		
		for (String sv_path : changed_sv_files) {
			SVDBFileTree ft = findRootFileTree(fBuildData, sv_path);
			if (ft != null) {
				plan.addFile(ft.getFilePath());
			}
		}
		
		return plan;
	}
	
	private ISVDBIndexChangePlan create_incr_argfile_plan(List<String> changed_f_files) {
		SVDBIndexChangePlanRebuildFiles plan = new SVDBIndexChangePlanRebuildFiles(this);
		
		plan.setFileListType(FileListType.Filelist);
	
		for (String f_path : changed_f_files) {
			plan.addFile(f_path);
		}
		
		return plan;
	}
	
	private ISVDBIndexChangePlan create_incr_hybrid_plan(
			List<String> changed_sv_files,
			List<String> changed_f_files) {
		SVDBIndexChangePlanRebuildFiles plan = new SVDBIndexChangePlanRebuildFiles(this);
		
		plan.setFileListType(FileListType.Hybrid);

		// Add argument files first
		for (String f_path : changed_f_files) {
			plan.addFile(f_path);
		}
		
		// Then add source files
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
	public void loadIndex(IProgressMonitor monitor) {
		
		if (fIndexBuilder != null) {
			SVDBIndexBuildJob build_job = null;
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
	
		if (!fIndexValid || !fIndexRefreshed) {
			SVDBIndexBuildJob build_job = null;
			
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
		if (fArgFileParser != null) {
			fArgFileParser.setFileSystemProvider(fs_provider);
		}

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
			fResolvedBaseLocation = SVFileUtils.resolvePath(fResolvedBaseLocation, 
					getBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
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
		return getFileList(monitor, FILE_ATTR_SRC_FILE);
	}
	
	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		checkInIndexOp("getFileList");

		return fBuildData.fIndexCacheData.getFileList(flags);
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
			int root_id = fBuildData.mapFilePathToId(root_path, false);
			
			if (root_path != null) {
				// Get the FileMap
				Map<Integer, SVDBFile> map = fBuildData.fCache.getSubFileMap(root_path);
				
				if (map == null) {
					// re-create the map
					SVDBFile file = fBuildData.fCache.getFile(new NullProgressMonitor(), root_path);
					
					if (file != null) {
						map = new HashMap<Integer, SVDBFile>();

						SVDBFile f = new SVDBFile(root_path);
						f.setLocation(SVDBLocation.pack(root_id, -1, -1));
						map.put(root_id, f);
						//					long start = System.currentTimeMillis();
						createSubFileMap(fBuildData, map, file, root_id, f);
						//					long end = System.currentTimeMillis();
						fBuildData.fCache.setSubFileMap(root_path, map);
						
					}
				}
				
				ret = (map != null)?map.get(id):null;
				
				
				
//				if (ret == null) {
//					System.out.println("id=" + id + " => null containsKey=" + map.containsKey(id));
//				}
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
			ISVDBAddChildItem				file) {
		
		for (ISVDBChildItem it : scope.getChildren()) {
			long l = it.getLocation();
			
			if (l != -1 && SVDBLocation.unpackFileId(l) != curr_id) {
				int new_id = SVDBLocation.unpackFileId(l);
				
				SVDBFile f = map.get(new_id);
				
				if (f == null) {
					f = new SVDBFile(build_data.mapFileIdToPath(new_id));
					f.setLocation(SVDBLocation.pack(new_id, -1, -1));
					map.put(new_id, f);
				}
				
				f.addChildItem(it);
				it.setParent(f);

				if (it instanceof ISVDBScopeItem) {
					createSubFileMap(build_data, map, (ISVDBChildParent)it, new_id, f);
				}
			} else {
				if (file != scope) {
					file.addChildItem(it);
				}
				
				if (it instanceof ISVDBScopeItem) {
					createSubFileMap(build_data, map, (ISVDBScopeItem)it, curr_id, (ISVDBScopeItem)it);
				}
			}
		}
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
			if (build_data.fIndexCacheData.fArgFilePaths.contains(path)) {
				// This is an argfile path
				ret = build_data.fCache.getFileTree(new NullProgressMonitor(), path, true);
			} else {
				boolean is_root = false;
				Map<String, List<String>> inc_map = build_data.fIndexCacheData.fRootIncludeMap;
				String root = null;
				for (Entry<String, List<String>> e : inc_map.entrySet()) {
					if (e.getKey().equals(path)) {
						root = e.getKey();
						is_root = true;
						break;
					} else if (e.getValue().contains(path)) {
						root = e.getKey();
						break;
					}
				}

				if (root != null) {
					SVDBFileTree ft = build_data.fCache.getFileTree(
							new NullProgressMonitor(), root, false);
					if (ft != null) {
						if (is_root) {
							ret = ft;
						} else {
							ret = findTargetFileTree(ft, paths);
						}
					} else {
						fLog.error("Failed to obtain FileTree " + root + " from cache");
					}
				}
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
		
		long l = parent.getLocation();
		
		if (fDebugEn) {
			fLog.debug("--> extractFileContents " + SVDBItem.getName(parent) + 
					" l.file_id=" + ((l != -1)?SVDBLocation.unpackFileId(l):"null") + " " + file_id);
		}
	
		if (l != -1 && SVDBLocation.unpackFileId(l) == file_id) {
			ret.addChildItem(parent);
			found_file = true;
			if (fDebugEn) {
				fLog.debug("  -- foundFile(parent) ; add " + SVDBItem.getName(parent));
			}
		} else {
			for (ISVDBChildItem c : parent.getChildren()) {
				l = c.getLocation();
				if (l != -1 && SVDBLocation.unpackFileId(l) == file_id) {
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
	
		return fBuildData.fIndexCacheData.containsFile(path, 
				FILE_ATTR_SRC_FILE+FILE_ATTR_ARG_FILE);
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
			is_argfile = fBuildData.fIndexCacheData.containsFile(path, FILE_ATTR_ARG_FILE);
		}
		
		if (is_argfile) {
			synchronized (fBuildData) {
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
				
				if (ft != null) {
					target_ft = findTargetFileTree(ft, r_path);
					file_id = fBuildData.mapFilePathToId(r_path, false);
					root_markers = fBuildData.fCache.getMarkers(root_file);
				}
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
					if (m.getLocation() != -1 && 
							SVDBLocation.unpackFileId(m.getLocation()) == file_id) {
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
		
		if (markers == null) {
			markers = new ArrayList<SVDBMarker>();
		}
		
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

			SVParser f = new SVParser();
			f.setFileMapper(fReadOnlyFileMapper);
			
			SVDBFileTree ft = out.getFileTree();
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
			
//			cleanExtFileElements(file_id, file);
			end = System.currentTimeMillis();
			fLog.debug("<-- Parse " + r_path + " " + (end-start) + "ms");
			file_ft = ft.getSVDBFile();
		}
		
		return new Tuple<SVDBFile, SVDBFile>(file_ft, file);
	}
	
	public ISVStringPreProcessor createPreProc(
			String 				path,
			InputStream			in,
			int					limit_lineno) {
		ISVStringPreProcessor ret = null;

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
			
			int this_fileid = fReadOnlyFileMapper.mapFilePathToId(r_path, false);
			
			preproc.preprocess();
			
			List<SVDBMacroDef> macros = new ArrayList<SVDBMacroDef>();
			for (SVDBMacroDef m : preproc.getDefaultMacros()) {
				if (m.getLocation() == -1 || limit_lineno == -1 ||
						SVDBLocation.unpackFileId(m.getLocation()) != this_fileid ||
						SVDBLocation.unpackLineno(m.getLocation()) <= limit_lineno) {
					macros.add(m);
				}
			}
			
			ret = new SVStringPreProcessor(macros);
		}
			
		return ret;
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
			if (fDebugEn) {
				fLog.debug("calculateIncomingMacros: root file=" + ft.getFilePath());
			}
			// Collect macros up the inclusion tree
			collectRootFileTreeMacros(all_defs, ft);
		} else {
			if (fDebugEn) {
				fLog.debug("calculateIncomingMacros: failed to find target file for " + path);
			}
		}
		
		if (build_data.isMFCU()) {
			if (fDebugEn) {
				fLog.debug("calculateIncomingMacros: Collecting from previous root files");
			}
			// Determine the index in the root files
			SVDBFileTree root_ft = findRootFileTree(build_data, path);
		
			List<String> root_files = build_data.getRootFileList();
			
			if (root_ft != null && root_files != null) {
				int root_idx = root_files.indexOf(root_ft.getFilePath());

				// Step back through the root files and add in macro state
				for (int i=root_idx-1; i>=0; i--) {
					String root_file_path = root_files.get(i);
					root_ft = findRootFileTree(build_data, root_file_path);

					if (root_ft == null) {
						fLog.error("Failed to find FileTree for root_path: " + root_file_path);
						continue;
					}
					if (fDebugEn) {
						fLog.debug("calculateIncomingMacros: Collecting from previous root file " + root_file_path);
					}
					for (int j=root_ft.getIncludedFileTreeList().size(); j>=0; j--) {
						SVDBFileTreeMacroList ml = root_ft.fMacroSetList.get(j);

						for (SVDBMacroDef m : ml.getMacroList()) {
							if (!all_defs.containsKey(m.getName())) {
								all_defs.put(m.getName(), m);
							}
						}

						if (j < root_ft.getIncludedFileTreeList().size()) {
							SVDBFileTree inc_ft = root_ft.getIncludedFileTreeList().get(j);
							collectRootFileTreeMacros(all_defs, inc_ft);
						}
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

	/**
	 * Compute the include/list path to the specified file
	 */
	public List<SVDBFilePath> getFilePath(String path) {
		List<SVDBFilePath> ret = new ArrayList<SVDBFilePath>();
		
		path = SVFileUtils.resolvePath(path, getBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
		
		boolean is_argfile = fBuildData.fIndexCacheData.fArgFilePaths.contains(path);
		SVDBFileTree ft = findTargetFileTree(fBuildData, path);
		
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
			Tuple<SVDBFileTree, ISVDBItemBase> af_it = findContainingArgFile(
					fBuildData, top_file_path, is_argfile);
			
			while (af_it != null) {
				fp.addPath(af_it.first(), af_it.second());
				
				af_it = findContainingArgFile(fBuildData, af_it.first().getFilePath(), true);
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
	
	private ISVDBItemBase findIncStmt(ISVDBChildParent parent, String path) {
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
	 * Locate the argument file that includes the specified path
	 * 
	 * TODO: just brute forcing it for now
	 * 
	 * @param build_data
	 * @param path
	 * @return
	 */
	private Tuple<SVDBFileTree, ISVDBItemBase> findContainingArgFile(
			SVDBArgFileIndexBuildData	build_data, 
			String						path,
			boolean						is_argfile) {
		Tuple<SVDBFileTree, ISVDBItemBase> ret = null;
		
		for (String af_path  : build_data.fIndexCacheData.getFileList(FILE_ATTR_ARG_FILE)) {
			SVDBFileTree af_ft = build_data.fCache.getFileTree(new NullProgressMonitor(), af_path, true);
			SVDBFile af_f = build_data.fCache.getFile(new NullProgressMonitor(), af_path);
			
			for (ISVDBChildItem ci : af_f.getChildren()) {
				if (is_argfile) {
					if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
						SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
						if (stmt.getPath().equals(path)) {
							ret = new Tuple<SVDBFileTree, ISVDBItemBase>(af_ft, ci);
							break;
						}
					}					
				} else {
					if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
						SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt)ci;
						if (stmt.getPath().equals(path)) {
							ret = new Tuple<SVDBFileTree, ISVDBItemBase>(af_ft, ci);
							break;
						}
					}					
				}
			}
			
			if (ret != null) {
				break;
			}
		}
	
		return ret;
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
	 * 
	 * @param monitor
	 * @return
	 */
	public Iterable<String> getFileNames(IProgressMonitor monitor) {
		return getFileList(monitor, FILE_ATTR_SRC_FILE);
	}

	/**
	 * Add the global declarations from the specified scope to the declaration
	 * cache
	 * 
	 * @param filename
	 * @param scope
	 */
	protected void cacheDeclarations(
			SVDBArgFileIndexBuildData	build_data,
			SVDBFile 					file, 
			SVDBFileTree 				ft) {
		Map<String, List<SVDBDeclCacheItem>> decl_cache = build_data.getDeclCacheMap();
		String file_path = file.getFilePath();
//		SVDBRefCacheEntry ref_entry = build_data.get

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

		if (ft != null) {
			cacheFileTreeDeclarations(
					ft,
					file_item_list);
		}
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
		boolean is_root_scope = (scope == null || 
				scope.getType() == SVDBItemType.PackageDecl ||
				scope.getType() == SVDBItemType.File);

		if (fDebugEn) {
			fLog.debug("--> cacheFileDeclarations(file=" + curr_filename + ", " + scope);
			fLog.debug("  scope=" + ((scope != null)?scope.getType():"null"));
		}
		
		for (ISVDBChildItem item : scope.getChildren()) {
			if (fDebugEn) {
				fLog.debug("  item: " + item.getType() + " "
						+ SVDBItem.getName(item));
			}
			
			if (item.getLocation() != -1 && 
					SVDBLocation.unpackFileId(item.getLocation()) != curr_fileid &&
					SVDBLocation.unpackFileId(item.getLocation()) > 0) {
				curr_fileid = SVDBLocation.unpackFileId(item.getLocation());
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

				// Only save tasks/functions if we're in a root scope
				if (is_root_scope || !item.getType().isElemOf(SVDBItemType.Function, SVDBItemType.Task)) {
					if (decl_list != null) {
						fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
								+ ((ISVDBNamedItem) item).getName() + " to cache");
						decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
								((ISVDBNamedItem) item).getName(), item.getType(),
								false));
					}
				}
				if (pkg_decl_list != null) {
					fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
							+ ((ISVDBNamedItem) item).getName() + " to pkg_decl cache");
					pkg_decl_list.add(new SVDBDeclCacheItem(this, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							false));
				}
				
				// 'Global' declarations, such as classes, can be declared within Modules/Interfaces/Programs 
				// as well as packages. Scan through the top level of these elements
				if (item.getType().isElemOf(SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl)) {
					cacheFileDeclarations(build_data, curr_fileid, 
						decl_list, null, (ISVDBScopeItem)item, ft);
				}
			} else if (item.getType() == SVDBItemType.VarDeclStmt && is_root_scope) {
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
			} else if (item.getType() == SVDBItemType.TypedefStmt && is_root_scope) {
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
	
	private void cacheFileTreeDeclarations(
			SVDBFileTree				ft,
			List<SVDBDeclCacheItem>		file_item_list) {
	
		if (ft.getSVDBFile() != null) {
			for (ISVDBChildItem c : ft.getSVDBFile().getChildren()) {
				if (c.getType() == SVDBItemType.MacroDef) {
					SVDBMacroDef def = (SVDBMacroDef)c;
					SVDBDeclCacheItem item = new SVDBDeclCacheItem(this, 
							ft.getFilePath(),
							def.getName(),
							SVDBItemType.MacroDef,
							true);
					file_item_list.add(item);
				}
			}
		}
		
		for (SVDBFileTree ft_i : ft.getIncludedFileTreeList()) {
			cacheFileTreeDeclarations(ft_i, file_item_list);
		}
	}

	private void cacheReferences(SVDBArgFileIndexBuildData build_data, SVDBFile file) {
		Map<String, List<Integer>> ref_map = build_data.fIndexCacheData.getReferenceCacheMap();
		
		SVDBFileRefCollector collector = new SVDBFileRefCollector(ref_map);
		SVDBFileRefFinder finder = new SVDBFileRefFinder();
		finder.setRefVisitor(collector);
		
		finder.visit(file);

		/*
		System.out.println("--> cacheReferences " + file.getFilePath());
		for (Entry<String, List<Integer>> e : ref_map.entrySet()) {
			StringBuilder files = new StringBuilder();
			for (int file_id : e.getValue()) {
				files.append("" + file_id + " ");
			}
			System.out.println("key=" + e.getKey() + " " + files.toString());
		}
		System.out.println("<-- cacheReferences " + file.getFilePath());
		 */
	}

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

	public void findReferences(
			IProgressMonitor 		monitor,
			ISVDBRefSearchSpec		ref_spec,
			ISVDBRefVisitor			ref_visitor) {
		checkInIndexOp("findReferences");

		Map<String, List<Integer>> ref_map = fBuildData.fIndexCacheData.getReferenceCacheMap();
		List<Integer> file_list = ref_map.get(ref_spec.getName());
		
		if (file_list != null) {
			// Now, have a closer look
			if (ref_spec.getNameMatchType() == NameMatchType.Equals) {

				for (Integer file_id : file_list) {
					String filename = fBuildData.mapFileIdToPath(file_id);
					SVDBFile file = findFile(new NullProgressMonitor(), filename);
					
					if (file != null) {
						SVDBRefMatcher ref_matcher = new SVDBRefMatcher(ref_spec, ref_visitor);
						SVDBFileRefFinder finder = new SVDBFileRefFinder();
						finder.setRefVisitor(ref_matcher);
						finder.visit(file);
					}
				}
			} else if (ref_spec.getNameMatchType() == NameMatchType.MayContain) {
				// Caller is simply interested in whether there might be a match
				if (file_list.size() > 0) {
					ref_visitor.visitRef(ref_spec, null);
				}
			}
		}
	}

	/**
	 * Obtains the file path for a given 
	 */
	public String getFilePath(SVDBLocation loc) {
		return fBuildData.mapFileIdToPath(loc.getFileId());
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		
		checkInIndexOp("getDeclFile");

		SVDBFile file = null;
		
		// If this is a pre-processor item, then return the FileTree view of the
		// file
		if (item.isFileTreeItem()) {
			SVDBFileTree ft = findTargetFileTree(fBuildData, item.getFilename());
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

	private Map<String, SVDBMacroDef> parseFile(
			String 						path, 
			SVDBArgFileIndexBuildData 	build_data,
			Map<String, SVDBMacroDef>	defines) {
		long start, end;
		SVParser f = new SVParser();
		f.setFileMapper(build_data);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		InputStream in = fFileSystemProvider.openStream(path);

		start = System.currentTimeMillis();
		
		// Propagate defines to the pre-processor
		SVPreProcessor2 pp = new SVPreProcessor2(path, in, build_data, build_data);
		pp.setIndexStats(build_data.fIndexStats);

		// Pass in defines
		for (Entry<String, SVDBMacroDef> def : defines.entrySet()) {
			pp.setMacro(def.getValue());
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> PreProcess " + path);
		}
		SVPreProcOutput pp_out = pp.preprocess();
		end = System.currentTimeMillis();
		
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

		long parse_start = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> Parse " + path);
		}
		SVLanguageLevel language_level;
		
		if (build_data.getForceSV()) {
			language_level = SVLanguageLevel.SystemVerilog;
		} else {
			language_level = SVLanguageLevel.computeLanguageLevel(path);
		}
		
//		SVDBFile file = f.parse(language_level, pp_out, path, build_data.fRefCollector, markers);
		SVDBFile file = f.parse(language_level, pp_out, path, null, markers);
		long parse_end = System.currentTimeMillis();
		
		build_data.fIndexStats.incLastIndexParseTime(parse_end-parse_start);
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "<-- Parse " + path + ": " +
					(parse_end-parse_start) + "ms");
		}

		start = System.currentTimeMillis();
		cacheDeclarations(build_data, file, ft);
		end = System.currentTimeMillis();
		build_data.fIndexStats.incLastIndexDeclCacheTime(end-start);
		
		start = System.currentTimeMillis();
		cacheReferences(build_data, file);
		end = System.currentTimeMillis();
		build_data.fIndexStats.incLastIndexRefCacheTime(end-start);
		
		start = System.currentTimeMillis();
		long last_modified = fFileSystemProvider.getLastModifiedTime(path);
		build_data.fCache.setFile(path, file, false);
		build_data.fCache.setFileTree(path, ft, false);
		build_data.fCache.setMarkers(path, markers, false);
		build_data.fCache.setLastModified(path, last_modified, false);
		
		// Update source file attributes
		updateSrcFileAttr(build_data, ft, markers);

		end = System.currentTimeMillis();

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
	 * Crawl through the file-tree structure 
	 * @param build_data
	 * @param ft
	 */
	private void updateSrcFileAttr(
			SVDBArgFileIndexBuildData 	build_data, 
			SVDBFileTree				ft,
			List<SVDBMarker> 			markers) {
		Set<String> processed_files = new HashSet<String>();
		
		// First, crawl through the file-tree structure to clear/set 
		// marker attributes
		updateSrcFileAttr(build_data, ft);
		
		// Now, go through the marker list
		for (SVDBMarker m : markers) {
			if (m.getLocation() == -1) {
				continue;
			}
			String path = build_data.mapFileIdToPath(
					SVDBLocation.unpackFileId(m.getLocation()));
			if (!processed_files.contains(path)) {
				build_data.fIndexCacheData.setFileAttrBits(path, FILE_ATTR_HAS_MARKERS);
			}
		}
	}
	
	private void updateSrcFileAttr(
			SVDBArgFileIndexBuildData	build_data,
			SVDBFileTree				ft) {
		if (ft.fMarkers != null && ft.fMarkers.size() > 0) {
			build_data.fIndexCacheData.setFileAttrBits(
					ft.getFilePath(), FILE_ATTR_HAS_MARKERS);
		} else {
			build_data.fIndexCacheData.clrFileAttrBits(
					ft.getFilePath(), FILE_ATTR_HAS_MARKERS);
		}
	
		for (SVDBFileTree ft_i : ft.fIncludedFileTrees) {
			updateSrcFileAttr(build_data, ft_i);
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
		
		if (fDebugEn) {
			fLog.debug("--> collectRootFileTreeMacros: " + ft.getFilePath());
		}
	
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
			
			if (fDebugEn) {
				fLog.debug("  Search for file in parent " + p_ft.getFilePath() + " index=" + include_idx);
			}
			
			if (include_idx == -1) {
				break;
			}
			
			for (int i=include_idx; i>=0; i--) {
				// Collect the macros from defined at this level
				SVDBFileTree ft_i = p_ft.getIncludedFileTreeList().get(i);
				
				if (fDebugEn) {
					fLog.debug("  Process preceding file: " +  ft_i.getFilePath());
				}
				
				SVDBFileTreeMacroList ml = p_ft.fMacroSetList.get(i);
				
				for (SVDBMacroDef m : ml.getMacroList()) {
					if (fDebugEn) {
						fLog.debug("    Add macro: " + m.getName());
					}
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
		
		if (fDebugEn) {
			fLog.debug("<-- collectRootFileTreeMacros: " + ft.getFilePath());
		}
	}
	
	/**
	 * Collect macros defined by files included in the specified file tree
	 * 
	 * @param defines
	 * @param ft
	 */
	private void collectFileTreeMacros(Map<String, SVDBMacroDef> defines, SVDBFileTree ft) {
		if (fDebugEn) {
			fLog.debug("--> collectFileTreeMacros: " + ft.getFilePath());
		}

		for (int i=ft.fIncludedFileTrees.size(); i>=0; i--) {
			SVDBFileTreeMacroList ml = ft.fMacroSetList.get(i);
			
			for (SVDBMacroDef m : ml.getMacroList()) {
				if (fDebugEn) {
					fLog.debug("  -- collectFileTreeMacros: " + m.getName());
				}
				
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
		
		if (fDebugEn) {
			fLog.debug("<-- collectFileTreeMacros: " + ft.getFilePath());
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
	protected void buildIndex(
			IProgressMonitor 				monitor,
			SVDBArgFileIndexBuildData		build_data) {
		long start_time=-1, end_time=-1;
		int total_work = 1000000;
		int per_file_work = 0;
		
		monitor.beginTask("Build Index", total_work);

		// First, parse the argument files
		start_time = System.currentTimeMillis();
		
		fArgFileParser.discoverRootFiles(new SubProgressMonitor(monitor, 100), build_data);
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
		List<String> paths = build_data.fIndexCacheData.getFileList(
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_ROOT_FILE);
		List<String> libfile_paths = build_data.fIndexCacheData.getFileList(
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_LIB_FILE);
		Map<String, SVDBMacroDef> defines = new HashMap<String, SVDBMacroDef>();
		
		build_data.fIndexStats.setNumRootFiles(paths.size());
		
		int total_files = (paths.size()+libfile_paths.size());
		
		if (total_files > 0) {
			per_file_work = (total_work / total_files);
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
			
			if (fFileSystemProvider.fileExists(path) && !fFileSystemProvider.isDir(path)) {
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
		
		// Finally, parse library-file paths
		for (int i=0; i<libfile_paths.size(); i++) {
			String path = libfile_paths.get(i);
			
			if (fDebugEn) {
				fLog.debug(LEVEL_MID, "LibFile Path: " + path);
			}
			
			if (fFileSystemProvider.fileExists(path) && !fFileSystemProvider.isDir(path)) {
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
		
		end_time = System.currentTimeMillis();
		
		build_data.fIndexStats.incLastIndexTotalTime(end_time-start_time);
		
//		Map<String, List<Integer>> refMap = build_data.fRefCollector.getRefMap();
//		for (Entry<String, List<Integer>> ent : refMap.entrySet()) {
//			System.out.print(ent.getKey() + ": ");
//			for (Integer file : ent.getValue()) {
//				System.out.print(file + " ");
//			}
//			System.out.println();
//		}
	
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + getBaseLocation()
					+ ": Parse source files -- " + (end_time - start_time)
					+ "ms");
		}
		
		monitor.done();
	}

	public ISVPreProcessor createPreProcScanner(String path) {
		SVPreProcessor2 ret = null;
		
		path = SVFileUtils.resolvePath(path, getBaseLocation(), fFileSystemProvider, fInWorkspaceOk);
		
		checkInIndexOp("createPreProcScanner");
		SVDBFileTree ft = findTargetFileTree(fBuildData, path);
		
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
	
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		checkInIndexOp("findIncludeFiles");
		
//		List<String> inc_paths = fBuildData.getIncludePathList();

		return SVDBFindIncFileUtils.findIncludeFiles(
				this,
				fFileSystemProvider,
				fBuildData.getIncludePathList(),
				root, flags);
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
	
	public SVDBIndexStats getIndexStats() {
		return fBuildData.fIndexStats;
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
