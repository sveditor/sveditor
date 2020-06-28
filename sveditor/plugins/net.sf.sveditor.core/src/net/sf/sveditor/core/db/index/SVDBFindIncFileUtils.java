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
package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

/**
 * Core functionality for locating include-file proposals given
 * a set of include paths from the index and a starting point
 * from the caller
 * 
 * @author ballance
 *
 */
public class SVDBFindIncFileUtils {
	private static final int LogLevel = ILogLevel.LEVEL_MID;
	private static boolean				fDebugEn = true;
	private static LogHandle			fLog;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBFindIncFileUtils");
	}
	
	public static List<SVDBIncFileInfo> findIncludeFiles(
			ISVDBIndex							index,
			ISVDBFileSystemProvider				fs,
			List<String>						inc_paths,
			String								root,
			int									flags) {
		List<SVDBIncFileInfo> ret = new ArrayList<SVDBIncFileInfo>();
		List<String> sv_exts = SVCorePlugin.getDefault().getDefaultSVExts();
		List<String> af_exts = SVCorePlugin.getDefault().getDefaultArgFileExts();
		
		if (fDebugEn) {
			fLog.debug(LogLevel, "--> findIncludeFiles( root=" + root + " flags=" + flags + ")");
			for (String inc_p : inc_paths) {
				fLog.debug(LogLevel, "  inc_p=" + inc_p);
			}
			for (String ext : sv_exts) {
				fLog.debug(LogLevel, "  sv_ext=" + ext);
			}
		}
		
		if (root == null) {
			root = "";
		}
	
		String inc_subdir = null;
		String inc_leaf = null;
		int last_slash_idx = root.lastIndexOf('/');
		
		if (last_slash_idx == -1) {
			inc_leaf = root;
		} else {
			inc_subdir = root.substring(0, last_slash_idx);
			inc_leaf = root.substring(last_slash_idx+1);
		}
	
		for (String inc_path : inc_paths) {
			String dir;
			
			if (inc_subdir == null) {
				dir = inc_path;
			} else {
				dir = inc_path + "/" + inc_subdir;
			}
		
			List<String> files = fs.getFiles(dir);
			
			for (String file : files) {
				String inc_file = file.substring(dir.length()+1);
				
				if (!inc_file.startsWith(inc_leaf)) {
					continue;
				}
				
				String ext = null;
				int last_dot = file.lastIndexOf('.');
				
				if (last_dot != -1) {
					ext = file.substring(last_dot+1);
				}
				
				boolean should_add = false;
				SVDBIncFileInfo info = new SVDBIncFileInfo(index, inc_path, inc_file);
				
				if (fs.fileExists(file)) {
					if ((flags & ISVDBIndex.FIND_INC_ALL_FILES) != 0) {
						should_add = true;
					} else if (ext != null) {
						if ((flags & ISVDBIndex.FIND_INC_SV_FILES) != 0 && sv_exts.contains(ext)) {
							should_add = true;
						}

						if ((flags & ISVDBIndex.FIND_INC_ARG_FILES) != 0 && af_exts.contains(ext)) {
							should_add = true;
						}
					}
				} else if (fs.isDir(file)) {
					should_add = true;
				}
				
				if (should_add) {
					if (!ret.contains(info)) {
						ret.add(info);
					}
				}
			}
			
		}
		
		if (fDebugEn) {
			fLog.debug(LogLevel, "<-- findIncludeFiles( root=" + root + " flags=" + flags + ")");
			for (SVDBIncFileInfo r : ret) {
				fLog.debug(LogLevel, "  ret=" + r.getIncFile());
			}
		}
		
		return ret;
	}

}
