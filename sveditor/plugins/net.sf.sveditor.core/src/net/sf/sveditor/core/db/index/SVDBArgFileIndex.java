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


package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBArgFileIndex extends AbstractSVDBIndex {
	
	public SVDBArgFileIndex(
			String						project,
			String						root,
			ISVDBFileSystemProvider		fs_provider,
			ISVDBIndexCache				cache,
			SVDBIndexConfig				config) {
		super(project, root, fs_provider, cache, config);
		fInWorkspaceOk = (root.startsWith("${workspace_loc}"));
	}

	@Override
	protected String getLogName() {
		return "SVDBArgFileIndex";
	}

	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}
	
	@Override
	protected SVDBBaseIndexCacheData createIndexCacheData() {
		return new SVDBArgFileIndexCacheData(getBaseLocation());
	}
	
	@Override
	protected boolean checkCacheValid() {
		
		synchronized (getCache()) {
			for (String arg_file : getCache().getFileList(true)) {
				long ts = getFileSystemProvider().getLastModifiedTime(arg_file);
				long ts_c = getCache().getLastModified(arg_file);
				if (ts > ts_c) {
					fLog.debug("    arg_file " + arg_file + " ts=" + ts + " cached ts=" + ts_c);
					return false;
				}
			}
		}

		return super.checkCacheValid();
	}

	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		fLog.debug("discoverRootFiles - " + getBaseLocation());
		
		clearFilesList();
		clearIncludePaths();
		clearDefines();
		
		monitor.beginTask("Discover Root Files", 4);
		
		// Add an include path for the arg file location
		addIncludePath(getResolvedBaseLocationDir());
		
		String resolved_argfile_path = getResolvedBaseLocation();
		if (getFileSystemProvider().fileExists(resolved_argfile_path)) {
			// Top argument file is, by default, root
			processArgFile(new SubProgressMonitor(monitor, 4), 
					null, null, 
					getResolvedBaseLocationDir(),
					getResolvedBaseLocation(), false);
		} else {
			String msg = "Argument file \"" + getBaseLocation() + "\" (\"" + 
					getResolvedBaseLocation() + "\") does not exist";
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
			String				path,
			String				base_location_dir,
			Set<String>			processed_paths,
			List<SVDBMarker>	markers) {
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
			/*
			SVArgFileParser parser = new SVArgFileParser(
					SVFileUtils.getPathParent(getBaseLocation()),
					getResolvedBaseLocationDir(),
					getFileSystemProvider());
			 */
			parser.init(lexer, path);
		
			try {
				parser.parse(ret, markers);
			} catch (SVParseException e) {}

			
			processed_paths.add(resolved_path);
			
			synchronized (getCache()) {
				if (fDebugEn) {
					fLog.debug("File: " + resolved_path + " has " + markers.size() + " errors");
					for (SVDBMarker m : markers) {
						fLog.debug("  " + m.getMessage());
					}
				}
				getCache().setMarkers(resolved_path, markers, true);
				getCache().setFile(resolved_path, ret, true);
				getCache().setLastModified(resolved_path, last_modified, true);
				
				if (fDebugEn) {
					fLog.debug("File(cached): " + resolved_path + " has " + 
							getCache().getMarkers(resolved_path).size() + " errors");
				}
			}
		} else {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"File \"" + path + "\" (" + resolved_path + ") does not exist"));
		}

		return ret;
	}
	
	private void processArgFile(
			IProgressMonitor	monitor, 
			SVDBFileTree		parent,
			Set<String> 		processed_paths, 
			String				base_location_dir,
			String 				path,
			boolean				is_root) {
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
		SVDBFile argfile = parseArgFile(path, sub_base_location_dir,
				processed_paths, markers);
		
		if (parent != null) {
			ft.addIncludedByFile(parent.getFilePath());
			parent.addIncludedFile(path);
		}
	
		synchronized (getCache()) {
			getCache().setFile(path, argfile, true);
		}

		if (argfile != null) {

			for (ISVDBChildItem ci : argfile.getChildren()) {
				if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
					// Process the included file
					SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
					String sub_path = resolvePath(stmt.getPath(), fInWorkspaceOk);
					
					// TODO: handle monitor
					if (getFileSystemProvider().fileExists(sub_path)) {
						if (!processed_paths.contains(sub_path)) {
							processArgFile(new NullProgressMonitor(), 
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
					addIncludePath(stmt.getIncludePath());
				} else if (ci.getType() == SVDBItemType.ArgFileDefineStmt) {
					SVDBArgFileDefineStmt stmt = (SVDBArgFileDefineStmt)ci;
					addDefine(stmt.getKey(), stmt.getValue());
				} else if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
					SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt)ci;
					String res_f = resolvePath(stmt.getPath(), fInWorkspaceOk);

					if (getFileSystemProvider().fileExists(res_f)) {
						addFile(res_f, false);
					}
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
									addFile(file_p, false);
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
			synchronized (getCache()) {
				getCache().setMarkers(path, markers, true);
				getCache().setFileTree(path, ft, true);
			}
			
			// Propagate markers to filesystem
			propagateMarkers(path);
		} else {
			// Problem with root argument file
			// TODO: propagate markers
		}

		/*
		monitor.beginTask("Process arg file " + path, 4);
		
		if (in != null) {
			SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();
			
			synchronized (cd) {
				cd.getArgFilePaths().add(path);
				cd.getArgFileTimestamps().add(getFileSystemProvider().getLastModifiedTime(path));
			}
			
			ITextScanner sc = new InputStreamTextScanner(in, path);
			SVFScanner scanner = new SVFScanner();
		
			monitor.worked(1);
			try {
				scanner.scan(sc);
			} catch (Exception e) {
				fLog.error("Failed to read argument file \"" + 
						getResolvedBaseLocation() + "\"", e);
			}
			
			monitor.worked(1);
			for (String f : scanner.getFilePaths()) {
				String exp_f = SVDBIndexUtil.expandVars(f, fProjectName, fInWorkspaceOk);
				fLog.debug("[FILE PATH] " + f + " (" + exp_f + ")");
				String res_f = resolvePath(exp_f, fInWorkspaceOk);
				
				if (getFileSystemProvider().fileExists(res_f)) {
					addFile(res_f);
				} else {
					fLog.error("Expanded path \"" + exp_f + "\" does not exist");
				}
			}
			
			for (String lib_p : scanner.getLibPaths()) {
				String exp_p = SVDBIndexUtil.expandVars(lib_p, fProjectName, fInWorkspaceOk);
				fLog.debug("[LIB PATH] " + lib_p + " (" + exp_p + ")");
				String res_p = resolvePath(exp_p, fInWorkspaceOk);
				
				if (getFileSystemProvider().isDir(res_p)) {
					List<String> paths = getFileSystemProvider().getFiles(res_p);
					Set<String> exts = scanner.getSrcExts();
					for (String file_p : paths) {
						int last_dot = file_p.lastIndexOf('.');
						if (last_dot != -1) {
							String ext = file_p.substring(last_dot);
							if (exts.contains(ext)) {
								addFile(file_p);
							}
						}
					}
				} else {
					fLog.error("Expanded library path \"" + exp_p + "\" does not exist");
				}
			}
			
			monitor.worked(1);
			for (String inc : scanner.getIncludePaths()) {
				String inc_path = SVDBIndexUtil.expandVars(inc, fProjectName, fInWorkspaceOk);
				fLog.debug("[INC PATH] " + inc + " (" + inc_path + ")");
				
				addIncludePath(inc_path);
			}
			
			monitor.worked(1);
			for (Entry<String, String> entry : scanner.getDefineMap().entrySet()) {
				fLog.debug("[DEFINE] " + entry.getKey() + "=" + entry.getValue());
				addDefine(entry.getKey(), entry.getValue());
			}
			
			getFileSystemProvider().closeStream(in);
			
			for (String arg_file : scanner.getArgFilePaths()) {
				arg_file = SVFileUtils.normalize(arg_file);
				arg_file = SVDBIndexUtil.expandVars(arg_file, fProjectName, fInWorkspaceOk);
				if (!cd.getArgFilePaths().contains(arg_file)) {
					processArgFile(new SubProgressMonitor(monitor, 4), arg_file); 
				}
			}
			monitor.done();
		} else {
			monitor.done();
			fLog.error("failed to open file \"" + path + "\"");
		}
		 */
	}

	@Override
	public void dispose() {

		/*
		SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();
		synchronized (cd) {
			cd.getArgFileTimestamps().clear();
			for (String arg_file : cd.getArgFilePaths()) {
				long ts = getFileSystemProvider().getLastModifiedTime(arg_file);
				fLog.debug("Setting ArgFile Timestamp: " + arg_file + "=" + ts);
				cd.getArgFileTimestamps().add(ts);
			}
		}
		 */
		
		super.dispose();
	}

	@Override
	public void fileChanged(String path) {
		fLog.debug("File changed: " + path);
		synchronized (getCache()) {
			if (getCache().getFileList(true).contains(path)) {
				invalidateIndex(new NullProgressMonitor(), "Argument File Changed: " + path, false);
			}
		}
		/*
		if (path.equals(getResolvedBaseLocation())) {
			// Invalidate, since this is the root file
			invalidateIndex(new NullProgressMonitor(), "Argument File Changed: " + path, false);
		}
		 */
		super.fileChanged(path);
	}
}
