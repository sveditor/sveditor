package net.sf.sveditor.core.db.index.argfile;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import net.sf.sveditor.core.builder.ISVBuilderOutput;
import net.sf.sveditor.core.builder.SVBuilderPreProcTracker;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBDeclCacheFileAttr;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBDeclCacheBuilder;
import net.sf.sveditor.core.db.index.SVDBFileCacheData;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.index.SVDBIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBIndexChangeDelta;
import net.sf.sveditor.core.db.index.SVDBIndexChangeEvent;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles.FileListType;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;

public class SVDBArgFileIndexRebuilder implements ISVDBDeclCacheFileAttr {
	private static LogHandle			fLog;
	private static boolean				fDebugEn;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBArgFileIndexRebuilder");
		fDebugEn = fLog.getDebugLevel() > 0;
		fLog.addLogLevelListener(new ILogLevelListener() {
			
			@Override
			public void logLevelChanged(ILogHandle handle) {
				fDebugEn = handle.getDebugLevel() > 0;
			}
		});
	}
	
	static void rebuild_files(
			SVDBArgFileIndex				index,
			SVDBArgFileIndexBuildData		build_data_i,
			IProgressMonitor				monitor,
			ISVBuilderOutput				out,
			SVDBIndexChangePlanRebuildFiles	plan) {
		SubMonitor subMonitor = SubMonitor.convert(monitor, 
				"Update " + index.getBaseLocation(), 2*1000*plan.getFileList().size());
		SVDBIndexChangeEvent ev = new SVDBIndexChangeEvent(
						SVDBIndexChangeEvent.Type.IncrRebuild, index);
	
		// Create new build data and a new cache
		SVDBArgFileIndexBuildData build_data = index.createBuildData();
		try {
		
			synchronized (build_data_i) {
				// Must initialize the file mapper state so any
				// new files are given correct numberings
				build_data.initFileMapperState(build_data_i);
			}

			if (plan.getFileListType() == FileListType.Source) {
				// simple: already have it
				out.note("Only source (SV) files have changed");
				if (fDebugEn) {
					fLog.debug("Only source (SV) files have changed");
				}
				process_root_files(
						index,
						build_data, 
						subMonitor,
						out, 
						ev,
						plan.getFileList());

				subMonitor.worked(1000);
			} else if (plan.getFileListType() == FileListType.Filelist) {

				out.note("Only filelist (.f) files have changed (TODO)");
				if (fDebugEn) {
					fLog.debug("Only filelist (.f) files have changed (TODO)");
				}
				process_root_filelists(
						index,
						build_data,
						subMonitor,
						out,
						ev,
						plan.getFileList());

				out.note("Only filelist (.f) files have changed");
				if (fDebugEn) {
					fLog.debug("Only filelist (.f) files have changed");
				}
			} else if (plan.getFileListType() == FileListType.Hybrid) {
				// Both filelists and files changed
				out.note("Both source (SV) and filelist (.f) files have changed (TODO)");
				if (fDebugEn) {
					fLog.debug("Both source (SV) and filelist (.f) files have changed (TODO)");
				}
			} else {
				if (fDebugEn) {
					fLog.debug("Unknown type of filelist: " + plan.getFileListType());
				}
			}

			// Once we have performed the required processing,
			// patch the new information into the existing cache
			update_cache(plan.getFileList(), build_data_i, build_data);

			// Once everything is done, fire the index-change event
			if (ev != null) {
				index.sendIndexChangeEv(ev);
			}
		} finally {
			// No matter what, need to dispose of the new cache
			if (build_data.getCache() != null) {
				build_data.getCache().dispose();
			}
		}
	}
	
	private static void update_cache(
			List<String>					processed_files,
			SVDBArgFileIndexBuildData		build_data_i,
			SVDBArgFileIndexBuildData		build_data) {
		if (fDebugEn) {
			fLog.debug("update_cache: back-patching index after incremental re-index");
		}
		synchronized (build_data_i) {
			// Cached data is stored per-file. 
			// - Go through the files processed during the last index operation
			// - If present in the master cache, remove
			// - Add to the master cache
			SVDBIndexCacheData old_cache_data = build_data_i.getIndexCacheData();
			ISVDBIndexCache	old_cache = build_data_i.getCache();
			SVDBIndexCacheData new_cache_data = build_data.getIndexCacheData();
			ISVDBIndexCache	new_cache = build_data.getCache();
			
			// First, remove any files from the filelist that no longer exist
			for (String path : processed_files) {
				if (!new_cache_data.containsFile(path, 0)) {
					if (fDebugEn) {
						fLog.debug("Removing file");
					}
					remove_file(build_data_i, path);
				}
			}
			for (SVDBFileCacheData cd : new_cache_data.getFileCacheData().values()) {
				String new_path = new_cache_data.mapFileIdToPath(cd.getFileId());
				SVDBFileCacheData old_cd = old_cache_data.getFileCacheData(new_path);
			
				if (fDebugEn) {
					fLog.debug("Checking whether newly-indexed file is present in old index: "
							+ new_path + " (" + old_cache_data.containsFile(new_path, 0) + ")");
				}
				
				if ((cd.getFileAttr() & FILE_ATTR_ROOT_FILE) != 0) {
					// Determine any that are no longer referenced and remove them
					if (old_cache_data.containsFile(new_path, 0)) {
						// TODO: this only works for source files now
						int n_orphan_files = 0;
						if (fDebugEn) {
							fLog.debug("  Pruning orphan include files");
						}
						
						// Collect included files from the original source file
						if (old_cd != null) {
							Set<String> old_included_files = new HashSet<String>();
							Set<String> new_included_files = new HashSet<String>();
							find_included_files(
									old_included_files,
									old_cache_data,
									old_cd);
							find_included_files(
									new_included_files,
									new_cache_data,
									cd);
							
							// Remove all files that now exist
							old_included_files.removeAll(new_included_files);
							for (String orphan_path : old_included_files) {
								if (fDebugEn) {
									fLog.debug("  Removing orphan path: " + orphan_path);
								}
								n_orphan_files++;
								old_cache_data.removeFileCacheData(orphan_path);
								old_cache.removeFile(orphan_path, false);
							}
							if (fDebugEn) {
								fLog.debug("  Done: " + n_orphan_files + " files pruned");
							}
							remove_cache_data(build_data_i, new_path);
							add_cache_data(build_data_i, build_data, new_path);
						} else {
							if (fDebugEn) {
								fLog.debug("  Completely new root file");
							}
							add_cache_data(build_data_i, build_data, new_path);
						}
					}
				} else {
					// Non-root file. This is pretty simple. 
					// Ensure that it's part of the old cache and update if needed
					if (old_cache_data.containsFile(new_path, 0)) {
						// Exists already. Determine how to update
						if (fDebugEn) {
							fLog.debug("  clearing old data");
						}
						remove_cache_data(build_data_i, new_path);
						add_cache_data(build_data_i, build_data, new_path);
					} else {
						if (fDebugEn) {
							fLog.debug("  adding new non-root data");
						}
						add_cache_data(build_data_i, build_data, new_path);
					}
				}
				// Finally, remove any processed files that are not present in the new cache
				for (String path : processed_files) {
					if (!new_cache_data.containsFile(path, 0)) {
						remove_cache_data(build_data_i, path);
					}
				}
			}
		}
	}
	
	private static void add_cache_data(
			SVDBArgFileIndexBuildData		build_data_i,
			SVDBArgFileIndexBuildData		build_data,
			String							path) {
		ISVDBIndexCache old_cache = build_data_i.getCache();
		ISVDBIndexCache new_cache = build_data.getCache();
		SVDBIndexCacheData old_cache_data = build_data_i.getIndexCacheData();
		SVDBIndexCacheData new_cache_data = build_data.getIndexCacheData();
		
		boolean is_argfile = (new_cache_data.getFileAttr(path) & FILE_ATTR_ARG_FILE) != 0;
		SVDBFileCacheData cd = new_cache_data.getFileCacheData(path);
		
		SVDBFileTree ft = new_cache.getFileTree(
				new NullProgressMonitor(), path, is_argfile);
		SVDBFile file = new_cache.getFile(
				new NullProgressMonitor(), path);
		List<SVDBMarker> markers = new_cache.getMarkers(path);

		old_cache_data.addFileCacheData(cd);
		old_cache.setFileTree(path, ft, is_argfile);
		old_cache.setFile(path, file, is_argfile);
		old_cache.setMarkers(path, markers, is_argfile);
	}
	
	private static void remove_cache_data(
			SVDBArgFileIndexBuildData		build_data,
			String							path) {
		ISVDBIndexCache cache = build_data.getCache();
		SVDBIndexCacheData cache_data = build_data.getIndexCacheData();
		boolean is_argfile = (cache_data.getFileAttr(path) & FILE_ATTR_ARG_FILE) != 0;
	
		cache.removeFile(path, is_argfile);
		cache_data.removeFileCacheData(path);
	}
	
	private static void find_included_files(
			Set<String>				included_files,
			SVDBIndexCacheData	cache_data,
			SVDBFileCacheData		cd) {
		for (SVDBFileCacheData cd_i : cache_data.getRootFilesCacheData()) {
			if (cd_i.getIncludedFiles().contains(cd.getFileId())) {
				if (!included_files.add(cache_data.mapFileIdToPath(cd_i.getFileId()))) {
					find_included_files(included_files, cache_data, cd_i);
				}
			}
		}
	}
			
			
	
	private static void process_root_files(
			SVDBArgFileIndex				index,
			SVDBArgFileIndexBuildData		build_data,
			SubMonitor						sub_monitor,
			ISVBuilderOutput				out,
			SVDBIndexChangeEvent			ev,
			List<String>					file_list) {
		
		for (String path : file_list) {
			SubMonitor loopMonitor = sub_monitor.newChild(1000);
			loopMonitor.beginTask("Parse " + path, 1000);
			
			SVDBFile file = process_root_file(index, build_data, loopMonitor, out, path);

		
			if (ev != null && file != null) {
				ev.addDelta(new SVDBIndexChangeDelta(
						SVDBIndexChangeDelta.Type.Change, file));
			}
			
			loopMonitor.worked(1000);
		}		
	}
	
	private static SVDBFile process_root_file(
			SVDBArgFileIndex				index,
			SVDBArgFileIndexBuildData		build_data,
			SubMonitor						sub_monitor,
			ISVBuilderOutput				out,
			String							path) {
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		
		// path is a 'root' file
		InputStream in = fs_provider.openStream(path);
		out.note("Parse: " + path);
		if (fDebugEn) {
			fLog.debug("Parse: " + path);
		}

//		if (!existing_files.remove(path)) { // Remove the new path from the set of pre-existing ones
//			added_files.add(path);
//		}
		
		if (in == null) {
			if (fDebugEn) {
				fLog.debug("Error: in is null");
			}
			return null;
		}
		
		SVDBFileCacheData cd = build_data.addFile(path, 
				FILE_ATTR_SRC_FILE+FILE_ATTR_ROOT_FILE);
		
		SVPreProcessor preproc = new SVPreProcessor(
				path, in, build_data, build_data);

		
		
//		synchronized (fBuildData) {
//			if (fBuildData.isMFCU()) {
//				List<SVDBMacroDef> macros = 
//						SVDBArgFileBuildDataUtils.calculateIncomingMacros(
//								fBuildData, path);
//
//				for (SVDBMacroDef d : macros) {
//					preproc.setMacro(d);
//				}
//			} else {
//				// Add global defines
//				for (Entry<String, String> e : fBuildData.getDefines().entrySet()) {
//					preproc.setMacro(new SVDBMacroDef(e.getKey(), e.getValue()));
//				}
//				for (Entry<String, String> e : build_data.getGlobalDefines().entrySet()) {
//					preproc.setMacro(new SVDBMacroDef(e.getKey(), e.getValue()));
//				}							
//			}
//		}
		
		SVDBDeclCacheBuilder decl_builder = new SVDBDeclCacheBuilder(
				cd.getTopLevelDeclarations(),
				index, // Used as the ISVDBDeclCacheInt handle
				cd.getIncludedFiles(),
				cd.getMissingIncludeFiles(),
				cd.getFileId());
		
		preproc.addListener(decl_builder);

		if (fDebugEn) {
			fLog.debug("--> preproc.preprocess");
		}
		SVPreProcOutput pp_out = preproc.preprocess();
		fs_provider.closeStream(in);
		if (fDebugEn) {
			fLog.debug("<-- preproc.preprocess: " + pp_out.toString());
		}
		pp_out.setFileChangeListener(
				new SVBuilderPreProcTracker(out, build_data));
		SVDBFileTree ft = decl_builder.getFileTree();
		
		// Collect include files
		List<String> included_files = new ArrayList<String>();
		SVDBFileTreeUtils.collectIncludedFiles(included_files, ft);
		
		SVParser f = new SVParser();
		f.setFileMapper(build_data);
		f.add_type_listener(decl_builder);
		
		SVLanguageLevel language_level;
		
		if (build_data.getForceSV()) {
			language_level = SVLanguageLevel.SystemVerilog;
		} else {
			language_level = SVLanguageLevel.computeLanguageLevel(path);
		}
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = f.parse(language_level, pp_out, path, markers);
		
		// Now, set the new root-file info to the cache
		build_data.getCache().setFile(path, file, false);
		build_data.getCache().setFileTree(path, ft, false);
		build_data.getCache().setMarkers(path, markers, false);
		long last_modified = fs_provider.getLastModifiedTime(path);
		build_data.getCache().setLastModified(path, last_modified, false);
		
		return file;
	}

	private static void process_root_filelists(
			SVDBArgFileIndex				index,
			SVDBArgFileIndexBuildData		build_data,
			SubMonitor						sub_monitor,
			ISVBuilderOutput				out,
			SVDBIndexChangeEvent			ev,
			List<String>					file_list) {

		for (String path : file_list) {
			process_root_filelist(index, build_data, sub_monitor, out, ev, path);
		}
//		for (String f_file : plan.getFileList()) {
//			synchronized (build_data_i) {
//				SVDBFile argfile = build_data_i.getFile(m, f_file);
//				if (argfile != null && argfile instanceof SVDBArgFile) {
//					SVDBArgFileParser.collectSourceFiles(build_data_i, 
//							(SVDBArgFile)argfile, existing_files);
//				}
//			}
//		}
	
//		// Process the new versions of the argument files
//		Set<String> processed_paths = new HashSet<String>();
//		for (String f_file : plan.getFileList()) {
//			SVDBArgFile argfile = null;
//			synchronized (build_data_i) {
//				SVDBFile f = build_data_i.getFile(m, f_file);
//				if (f != null && f instanceof SVDBArgFile) {
//					argfile = (SVDBArgFile)f;
//				}
//			}
//			
//
//		}
	}
	
	private static void remove_file(
			SVDBArgFileIndexBuildData		build_data,
			String							path) {
		SVDBFileCacheData cd = build_data.getIndexCacheData().getFileCacheData(path);
		if (cd != null) {
			if (fDebugEn) {
				fLog.debug("Note: removing file \"" + path + "\" from index");
			}
			boolean is_argfile = (cd.getFileAttr() & FILE_ATTR_ARG_FILE) != 0;

			// Remove the file itself so we don't get phantom references
			// while removing included files
			build_data.removeFile(path, is_argfile);

			for (int inc_file_id : cd.getIncludedFiles()) {
				remove_included_file(build_data, inc_file_id);
			}
		} else {
			if (fDebugEn) {
				fLog.debug("Note: file \"" + path + "\" doesn't exist");
			}
		}
	}
	
	private static void remove_included_file(
			SVDBArgFileIndexBuildData		build_data,
			int								inc_file_id) {
		boolean found = false;
		SVDBFileCacheData inc_file_cd = 
				build_data.getIndexCacheData().getFileCacheData(inc_file_id);
		if (inc_file_cd != null) {
			if (fDebugEn) {
				fLog.debug("Note: Remove included file id=" + inc_file_id);
			}

			boolean is_argfile = (inc_file_cd.getFileAttr() & FILE_ATTR_ARG_FILE) != 0;

			for (SVDBFileCacheData cd : build_data.getIndexCacheData().getFileCacheData().values()) {
				if (cd.getIncludedFiles().contains(inc_file_id)) {
					found = true;
					break;
				}
			}

			if (!found) {
				if (fDebugEn) {
					fLog.debug("Removing orphan included file " +
							build_data.mapFileIdToPath(inc_file_id));
				}
				build_data.removeFile(build_data.mapFileIdToPath(inc_file_id), is_argfile);
				for (int inc_file_id_i : inc_file_cd.getIncludedFiles()) {
					remove_included_file(build_data, inc_file_id_i);
				}
			}
		} else {
			if (fDebugEn) {
				fLog.debug("Note: included file id=" + inc_file_id + " doesn't exist");
			}
		}
	}
	
	private static void process_root_filelist(
			SVDBArgFileIndex				index,
			SVDBArgFileIndexBuildData		build_data,
			SubMonitor						sub_monitor,
			ISVBuilderOutput				out,
			SVDBIndexChangeEvent			ev,
			String							path) {
		Set<String> processed_paths = new HashSet<String>();
		
		SVDBArgFileParser.processArgFile(
				sub_monitor.newChild(1000),
				build_data, 
				null, 
				processed_paths, 
				build_data.getBaseLocation(), // TODO:
//				(argfile != null)?argfile.getBaseLocation():build_data.getBaseLocation(),
				path, 
				true /*is root*/);
	}
}
