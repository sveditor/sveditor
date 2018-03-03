package net.sf.sveditor.core.db.index.argfile;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.index.ISVDBDeclCacheFileAttr;
import net.sf.sveditor.core.db.index.SVDBFileCacheData;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles.FileListType;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanType;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBArgFileChangePlanner implements ISVDBDeclCacheFileAttr {
	private static LogHandle			fLog;
	private static boolean				fDebugEn;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBArgFileChangePlanner");
		fDebugEn = (fLog.getDebugLevel() > 0);
		fLog.addLogLevelListener(new ILogLevelListener() {
			
			@Override
			public void logLevelChanged(ILogHandle handle) {
				fDebugEn = (fLog.getDebugLevel() > 0);
			}
		});
	}

	public static ISVDBIndexChangePlan createIndexChangePlan(
			SVDBArgFileIndex					index,
			SVDBArgFileIndexBuildData			build_data,
			List<SVDBIndexResourceChangeEvent> 	changes) {
		ISVDBIndexChangePlan plan = new SVDBIndexChangePlan(index, SVDBIndexChangePlanType.Empty);
		
		if (fDebugEn) {
			fLog.debug("--> createIndexChangePlan (incremental) size=" + changes.size());
		}
		List<String> changed_sv_files = new ArrayList<String>();
		List<String> changed_f_files = new ArrayList<String>();
		boolean files_added   = false;
		boolean files_changed = false;
		boolean files_removed = false;

//		SVDBIndexChangePlanRebuildFiles rebuild_sv_files_plan = new SVDBIndexChangePlanRebuildFiles(index);
//		SVDBIndexChangePlanRebuildFiles rebuild_arg_files_plan = new SVDBIndexChangePlanRebuildFiles(index);

		for (SVDBIndexResourceChangeEvent cev : changes) {
			String path = index.resolvePath(cev.getPath());
			if (fDebugEn) {
				fLog.debug("Changed file: " + path + " exists=" + build_data.containsFile(path, 0));
			}

			switch (cev.getType()) {
			case ADD: files_added = true; break;
			case CHANGE: files_changed = true; break;
			case REMOVE: files_removed = true; break;
			}

			// See if index file is already included by one of the root files,
			// or might be a missing file
			if (build_data.containsFile(path, FILE_ATTR_SRC_FILE)) {
				if (fDebugEn) {
					fLog.debug("  Is a Source File");
				}
				int attr = build_data.getFileAttr(path);
				if ((attr & FILE_ATTR_ROOT_FILE) != 0) {
					// 
					if (!changed_sv_files.contains(path)) {
						changed_sv_files.add(path);
					}
				} else {
					// Find and add root files that include this file
					add_root_files(path, build_data, changed_sv_files);
				}
			} else if (build_data.containsFile(path, FILE_ATTR_ARG_FILE)) {
				if (fDebugEn) {
					fLog.debug("  Is an argument file - rebuilding project");
				}
				// Argument file changed, so rebuild project
				if (!changed_f_files.contains(path)) {
					changed_f_files.add(path);
				}
				
//				int attr = build_data.getFileAttr(path);
//				if ((attr & FILE_ATTR_ROOT_FILE) != 0) {
//					if (!changed_f_files.contains(path)) {
//						changed_f_files.add(path);
//					}
//				} else {
//					// Find and add root files that include this file
//					add_root_files(path, build_data, changed_f_files);
//				}
			} else {
				// See if index is a missing file
				String leaf = SVFileUtils.getPathLeaf(path);
				for (SVDBFileCacheData cd : build_data.getIndexCacheData().getRootFilesCacheData()) {
					// Only check root files
					if ((cd.getFileAttr() & FILE_ATTR_ROOT_FILE) != 0) {
						if (cd.getMissingIncludeFiles().contains(leaf)) {
							String root_path = build_data.mapFileIdToPath(cd.getFileId());
							if ((cd.getFileAttr() & FILE_ATTR_SRC_FILE) != 0) {
								if (!changed_sv_files.contains(root_path)) {
									if (fDebugEn) {
										fLog.debug("Changed file " + path + " may be a missing include in " +
												root_path);
									}
									changed_sv_files.add(root_path);
								}
							} else {
								if (!changed_f_files.contains(root_path)) {
									changed_f_files.add(root_path);
								}
							}
						}
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("  changed_sv_files: " + changed_sv_files.size() + 
					" changed_f_files: " + changed_f_files.size());
		}

//		if (files_removed) {
//			if (files_added || files_changed) {
//				if (fDebugEn) {
//					fLog.debug("  Files were both removed and added/changed; Full rebuild");
//				}
//				plan = new SVDBIndexChangePlanRebuild(index);
//			} else {
//				if (fDebugEn) {
//					fLog.debug("  Files were removed");
//				}
//
//				SVDBIndexChangePlanRemoveFiles rf_plan = 
//						new SVDBIndexChangePlanRemoveFiles(index);
//
//				for (SVDBIndexResourceChangeEvent ev : changes) {
//					if (ev.getType() == Type.REMOVE) {
//						rf_plan.addFile(ev.getPath());
//					}
//				}
//
//				plan = rf_plan;
//			}
//		} else {
		if (changed_f_files.size() > 0) {
			// For now, rebuild any time a filelist changes
			plan = new SVDBIndexChangePlanRebuild(index);
		} else if (changed_sv_files.size() > 0) {
			plan = create_incr_plan(index, build_data, changed_sv_files);
		}

		/*
				if (changed_f_files.size() > 0) {
					// TODO: Full build for now
					plan = new SVDBIndexChangePlanRebuild(index);
				} else if (changed_sv_files.size() > 0) {
					plan = create_incr_plan(changed_sv_files);
				}
		 */
		if (fDebugEn) {
			fLog.debug("<-- createIndexChangePlan (incremental)");
		}
		
		return plan;
	}

	private static ISVDBIndexChangePlan create_incr_plan(
			SVDBArgFileIndex			index,
			SVDBArgFileIndexBuildData	build_data,
			List<String> 				changed_sv_files) {
		SVDBIndexChangePlanRebuildFiles plan = new SVDBIndexChangePlanRebuildFiles(index);
	
		plan.setFileListType(FileListType.Source);
		
		for (String sv_path : changed_sv_files) {
			plan.addFile(sv_path);
		}
		
		return plan;
	}
	
	private static ISVDBIndexChangePlan create_incr_argfile_plan(
			SVDBArgFileIndex			index,
			SVDBArgFileIndexBuildData	build_data,
			List<String> 				changed_f_files) {
		SVDBIndexChangePlanRebuildFiles plan = new SVDBIndexChangePlanRebuildFiles(index);
		
		plan.setFileListType(FileListType.Filelist);
	
		for (String f_path : changed_f_files) {
			plan.addFile(f_path);
		}
		
		return plan;
	}
	
	private static ISVDBIndexChangePlan create_incr_hybrid_plan(
			SVDBArgFileIndex			index,
			SVDBArgFileIndexBuildData	build_data,
			List<String> 				changed_sv_files,
			List<String> 				changed_f_files) {
		SVDBIndexChangePlanRebuildFiles plan = new SVDBIndexChangePlanRebuildFiles(index);
		
		plan.setFileListType(FileListType.Hybrid);

		// Add argument files first
		for (String f_path : changed_f_files) {
			plan.addFile(f_path);
		}
		
		// Then add source files
		for (String sv_path : changed_sv_files) {
			SVDBFileTree ft = SVDBArgFileBuildDataUtils.findRootFileTree(
					build_data, sv_path);
			if (ft != null) {
				plan.addFile(ft.getFilePath());
			}
		}
		
		return plan;
	}
	
	private static int add_root_files(
			String						path,
			SVDBArgFileIndexBuildData	build_data,
			List<String>				paths) {
		Set<Integer>		processed_files = new HashSet<Integer>();
		int file_id = build_data.mapFilePathToId(path, false);
		SVDBFileCacheData cd = build_data.getIndexCacheData().getFileCacheData(file_id);
		
		return add_root_files(processed_files, cd, build_data, paths);
	}
	
	private static int add_root_files(
			Set<Integer>				processed_files,
			SVDBFileCacheData			cd,
			SVDBArgFileIndexBuildData	build_data,
			List<String>				paths) {
		int added = 0;

		for (SVDBFileCacheData cd_i : build_data.getIndexCacheData().getFileCacheData().values()) {
			if (cd_i.getIncludedFiles().contains(cd.getFileId())) {
				if ((cd_i.getFileAttr() & FILE_ATTR_ROOT_FILE) != 0) {
					String path_i = build_data.mapFileIdToPath(cd_i.getFileId());
					if (!paths.contains(path_i)) {
						paths.add(path_i);
						added++;
					}
				} else {
					// Recurse
					if (!processed_files.add(cd_i.getFileId())) {
						add_root_files(processed_files, cd_i, build_data, paths);
					} else {
						fLog.error("Prevented recursion while finding root files");
					}
				}
			}
		}
		
		return added;
	}

}
