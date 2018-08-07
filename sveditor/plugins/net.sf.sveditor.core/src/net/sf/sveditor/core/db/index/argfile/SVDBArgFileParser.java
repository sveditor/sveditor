package net.sf.sveditor.core.db.index.argfile;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBArgFile;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.index.ISVDBDeclCacheFileAttr;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBFileCacheData;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

public class SVDBArgFileParser implements ILogLevelListener {
	private static boolean				fDebugEn;
	private static LogHandle			fLog;
	
	private ISVDBFileSystemProvider		fFSProvider;
	private IProject					fProject;
	private String						fProjectName;
	private String						fBaseLocation;
	private String						fResolvedBaseLocation;
	private String						fResolvedBaseLocationDir;
	private boolean						fInWorkspaceOk = true;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBArgFileParser");
		fDebugEn = fLog.getDebugLevel() > 0;
		fLog.addLogLevelListener(new ILogLevelListener() {
			
			@Override
			public void logLevelChanged(ILogHandle handle) {
				fDebugEn = handle.getDebugLevel() > 0;
			}
		});
	}
	
	
	public SVDBArgFileParser(
			ISVDBFileSystemProvider 	fs_provider,
			String						base_location,
			String						resolved_base_location,
			String						resolved_base_location_dir,
			IProject					project) {
		fLog = LogFactory.getLogHandle("SVDBArgFileParser");
		fDebugEn = fLog.isEnabled();
		fFSProvider = fs_provider;
		fBaseLocation = base_location;
		fResolvedBaseLocation = resolved_base_location;
		fResolvedBaseLocationDir = resolved_base_location_dir;
		fProject = project;
		fProjectName = (project != null)?project.getName():null;
	}
	
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFSProvider = fs_provider;
	}
	
	
	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	/**
	 * Collects source files given a fully-parsed tree of
	 * argument files.
	 * 
	 * @param build_data
	 * @param argfile
	 * @param src_files
	 */
	public static void collectSourceFiles(
			SVDBArgFileIndexBuildData	build_data,
			SVDBArgFile					argfile,
			List<String>				src_files) {
		Set<String> processed_files = new HashSet<String>();
		collectSourceFiles(build_data, argfile, processed_files, src_files);
	}
	
	private static void collectSourceFiles(
			SVDBArgFileIndexBuildData	build_data,
			SVDBArgFile					argfile,
			Set<String>					processed_files,
			List<String>				src_files) {
		String sub_base_location_dir = argfile.getBaseLocation();
//		System.out.println("sub_base_location: " + sub_base_location_dir);
		
		for (ISVDBChildItem ci : argfile.getChildren()) {
			if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
				// Process the included file
				SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
				String sub_path = build_data.resolvePath(
						stmt.getPath(), sub_base_location_dir);
			
				if (processed_files.add(sub_path)) {
					SVDBFile sub_argfile = build_data.getFile(new NullProgressMonitor(), sub_path);
					if (sub_argfile != null) {
						collectSourceFiles(build_data, (SVDBArgFile)sub_argfile, 
								processed_files, src_files);
					}
				}
			} else if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
				SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt)ci;
				String res_f = build_data.resolvePath(
						stmt.getPath(), sub_base_location_dir);

				src_files.add(res_f);
			} else if (ci.getType() == SVDBItemType.ArgFileSrcLibPathStmt) {
				SVDBArgFileSrcLibPathStmt stmt = (SVDBArgFileSrcLibPathStmt)ci;

				fLog.debug(LEVEL_MID, "Processing source-library path " + stmt.getSrcLibPath());
				if (build_data.getFSProvider().isDir(stmt.getSrcLibPath())) {
					List<String> paths = build_data.getFSProvider().getFiles(stmt.getSrcLibPath());
					Set<String> exts = SVFScanner.getSrcExts();
					for (String file_p : paths) {
						fLog.debug(LEVEL_MID, "  Processing child path: " + file_p);
						int last_dot = file_p.lastIndexOf('.');
						if (last_dot != -1) {
							String ext = file_p.substring(last_dot);
							if (exts.contains(ext)) {
								fLog.debug(LEVEL_MID, "  -> Adding to source file list");
								src_files.add(file_p);
							}
						}
					}
				}
			} else if (ci.getType() == SVDBItemType.ArgFileSrcLibFileStmt) {
//				SVDBArgFileSrcLibFileStmt stmt = (SVDBArgFileSrcLibFileStmt)ci;
//				if (!lib_files.contains(stmt.getSrcLibFile())) {
//					lib_files.add(stmt.getSrcLibFile());
//				}
			}
		}		
	}
			
	
//	public void computeArgFileDelta(
//			SVDBArgFileIndexBuildData	build_data,
//			String						base_location,
//			List<String>				source_files,
//			List<String>				removed_source_files,
//			String						argfile) {
//		Set<String> processed_argfiles = new HashSet<String>();
//		
//		computeArgFileDelta(build_data, base_location, processed_argfiles, 
//				source_files, removed_source_files, argfile);
//	}
	
	private void computeArgFileDelta(
			SVDBArgFileIndexBuildData	build_data,
			String						base_location,
			Set<String>					processed_argfiles,
			List<String>				source_files,
			List<String>				removed_source_files,
			String						argfile) {
		if (processed_argfiles.contains(argfile)) {
			return;
		} else {
			processed_argfiles.add(argfile);
			
			// Parse argument file and add source files
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVDBFile svdb_argfile = parseArgFile(
					build_data, argfile, base_location, 
					processed_argfiles, markers);
		}		
	}
	
	public void discoverRootFiles(
			IProgressMonitor 			monitor,
			SVDBArgFileIndexBuildData	build_data) {
		fLog.debug("discoverRootFiles - " + fBaseLocation);

		
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Discover Root Files", 4);

		// Add an include path for the arg file location
		build_data.addIncludePath(fResolvedBaseLocationDir);

		String resolved_argfile_path = fResolvedBaseLocation;
		if (fFSProvider.fileExists(resolved_argfile_path)) {
			processArgFile(
					subMonitor.newChild(4), 
					build_data,
					null, 
					null, 
					fResolvedBaseLocationDir,
					fResolvedBaseLocation,
					false);
		} else {
			String msg = "Argument file \"" + fBaseLocation + "\" (\""
					+ fResolvedBaseLocationDir + "\") does not exist";
			fLog.error(msg);
			if (fProjectName != null) {
				// TODO: must save this somewhere...
				fFSProvider.addMarker(
						"${workspace_loc}/" + fProjectName,
						ISVDBFileSystemProvider.MARKER_TYPE_ERROR, 0, msg);
			}
		}

		subMonitor.done();
	}	

	public static SVDBArgFile parseArgFile(
			SVDBArgFileIndexBuildData	build_data,
			String						path,
			String						base_location_dir,
			Set<String>					processed_paths,
			List<SVDBMarker>			markers) {
		SVDBArgFile ret = new SVDBArgFile(path, base_location_dir);
		InputStream in = null;
		
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		
		String resolved_path = SVFileUtils.resolvePath(
				path, base_location_dir, fs_provider, true);
	
		if (processed_paths.contains(resolved_path)) {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"Multiple inclusion of file \"" + resolved_path + "\" (from " + path + ")"));
		} else if ((in = fs_provider.openStream(resolved_path)) != null) {
			long last_modified = fs_provider.getLastModifiedTime(resolved_path);
			processed_paths.add(resolved_path);
			ISVArgFileVariableProvider vp = SVCorePlugin.getVariableProvider(build_data.getProject());
			SVArgFilePreProcessor pp = new SVArgFilePreProcessor(
					in, resolved_path, vp);
			
			SVArgFilePreProcOutput pp_out = pp.preprocess();
			
			SVArgFileLexer lexer = new SVArgFileLexer();
			lexer.init(null, pp_out);
			
			SVArgFileParser parser = new SVArgFileParser(
					base_location_dir, base_location_dir,
					fs_provider);
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
			build_data.setMarkers(resolved_path, markers, true);
			build_data.setFile(resolved_path, ret, true);
			build_data.setLastModified(resolved_path, last_modified, true);

			if (fDebugEn) {
				fLog.debug("File(cached): " + resolved_path + " has " + 
						build_data.getMarkers(resolved_path).size() + " errors");
			}
		} else {
			ret = null;
			markers.add(new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
					"File \"" + path + "\" (" + resolved_path + ") does not exist"));
		}

		return ret;
	}
	
	private void collectArgFilePaths(
			SVDBFile				argfile,
			String					sub_base_location_dir,
			List<String>			incdirs,
			List<String>			src_files,
			List<String>			arg_files,
			List<String>			lib_files) {
		
		for (ISVDBChildItem ci : argfile.getChildren()) {
			if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
				// Process the included file
				SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
				String sub_path = SVFileUtils.resolvePath(stmt.getPath(), sub_base_location_dir, fFSProvider, fInWorkspaceOk);
				
				if (!arg_files.contains(sub_path)) {
					arg_files.add(sub_path);
				}
			} else if (ci.getType() == SVDBItemType.ArgFileIncDirStmt) {
				SVDBArgFileIncDirStmt stmt = (SVDBArgFileIncDirStmt)ci;
				if (!incdirs.contains(stmt.getIncludePath())) {
					incdirs.add(stmt.getIncludePath());
				}
			} else if (ci.getType() == SVDBItemType.ArgFilePathStmt) {
				SVDBArgFilePathStmt stmt = (SVDBArgFilePathStmt)ci;
				String res_f = SVFileUtils.resolvePath(stmt.getPath(), 
						sub_base_location_dir, fFSProvider, fInWorkspaceOk);

				if (fFSProvider.fileExists(res_f)) {
					if (!src_files.contains(res_f)) {
						src_files.add(res_f);
					}
				}
			} else if (ci.getType() == SVDBItemType.ArgFileSrcLibPathStmt) {
				SVDBArgFileSrcLibPathStmt stmt = (SVDBArgFileSrcLibPathStmt)ci;

				if (fFSProvider.isDir(stmt.getSrcLibPath())) {
					List<String> paths = fFSProvider.getFiles(stmt.getSrcLibPath());
					Set<String> exts = SVFScanner.getSrcExts();
					for (String file_p : paths) {
						int last_dot = file_p.lastIndexOf('.');
						if (last_dot != -1) {
							String ext = file_p.substring(last_dot);
							if (exts.contains(ext)) {
								if (!lib_files.contains(file_p)) {
									lib_files.add(file_p);
								}
							}
						}
					}
				}
			} else if (ci.getType() == SVDBItemType.ArgFileSrcLibFileStmt) {
				SVDBArgFileSrcLibFileStmt stmt = (SVDBArgFileSrcLibFileStmt)ci;
				if (!lib_files.contains(stmt.getSrcLibFile())) {
					lib_files.add(stmt.getSrcLibFile());
				}
			}
		}
	}
	
	public static void processArgFile(
			IProgressMonitor				monitor, 
			SVDBArgFileIndexBuildData		build_data,
			SVDBFileTree					parent,
			Set<String> 					processed_paths, 
			String							base_location_dir,
			String 							path,
			boolean							is_root) {
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		path = build_data.resolvePath(
				path, build_data.getResolvedBaseLocationDir());

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
		SVDBArgFile argfile = parseArgFile(build_data, path, 
				sub_base_location_dir, processed_paths, markers);
		
		int attr = ISVDBDeclCacheFileAttr.FILE_ATTR_ARG_FILE;
		if (parent != null) {
			ft.addIncludedByFile(parent.getFilePath());
			parent.addIncludedFile(path);
			attr += ISVDBDeclCacheFileAttr.FILE_ATTR_ROOT_FILE;
		}

		long last_modified = fs_provider.getLastModifiedTime(path);
		build_data.setFile(path, argfile, true);
		build_data.setLastModified(path, last_modified, true);

		if (argfile != null) {
			SVDBFileCacheData cd = build_data.addFile(path, attr);
			build_data.setFile(path, argfile, true);

			for (ISVDBChildItem ci : argfile.getChildren()) {
				if (ci.getType() == SVDBItemType.ArgFileIncFileStmt) {
					// Process the included file
					SVDBArgFileIncFileStmt stmt = (SVDBArgFileIncFileStmt)ci;
					String sub_path = build_data.resolvePath(
							stmt.getPath(), sub_base_location_dir);
					
					// TODO: handle monitor
					if (fs_provider.fileExists(sub_path)) {
						if (!processed_paths.contains(sub_path)) {
							processArgFile(new NullProgressMonitor(), build_data,
									ft, processed_paths, sub_base_location_dir, 
									sub_path, stmt.isRootInclude());
						} else {
							SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
									"Multiple inclusion of file \"" + sub_path + "\" (from " + path + ")");
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
					String res_f = build_data.resolvePath(
							stmt.getPath(), sub_base_location_dir);

					if (fs_provider.fileExists(res_f)) {
						// Here is where we need to determine what type of file this is
						Set<String> sv_exts = SVCorePlugin.getDefault().getDefaultSVExts();
						Set<String> vh_exts = SVCorePlugin.getDefault().getDefaultVHDLExts();
						String ext = SVFileUtils.getPathExt(res_f);
						
						int file_a = 
								ISVDBDeclCacheFileAttr.FILE_ATTR_SRC_FILE +
								ISVDBDeclCacheFileAttr.FILE_ATTR_ROOT_FILE;
						
						if (sv_exts.contains(ext)) {
							file_a += ISVDBDeclCacheFileAttr.FILE_ATTR_SV_FILE;
						} else if (vh_exts.contains(ext)) {
							file_a += ISVDBDeclCacheFileAttr.FILE_ATTR_VH_FILE;
						} else {
							SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.SemanticError, 
								"File " + res_f + " has unrecognized extension");
							m.setLocation(stmt.getLocation());
							markers.add(m);
						}
						build_data.addFile(res_f, file_a);
					}
				} else if (ci.getType() == SVDBItemType.ArgFileMfcuStmt) {
					build_data.setMFCU();
				} else if (ci.getType() == SVDBItemType.ArgFileForceSvStmt) {
					build_data.setForceSV(true);
				} else if (ci.getType() == SVDBItemType.ArgFileSrcLibPathStmt) {
					SVDBArgFileSrcLibPathStmt stmt = (SVDBArgFileSrcLibPathStmt)ci;

					String res_p = build_data.resolvePath(
							stmt.getSrcLibPath(), sub_base_location_dir);
					fLog.debug(LEVEL_MID, "Processing LibPath " + res_p + 
							" (sub_base_location_dir=" + sub_base_location_dir + ")");
					if (fs_provider.isDir(res_p)) {
						List<String> paths = fs_provider.getFiles(res_p);
						Set<String> exts = SVFScanner.getSrcExts();
						for (String file_p : paths) {
							fLog.debug(LEVEL_MID, "  Processing LibPath file " + file_p);
							int last_dot = file_p.lastIndexOf('.');
							if (last_dot != -1) {
								String ext = file_p.substring(last_dot);
								if (exts.contains(ext)) {
									fLog.debug(LEVEL_MID, "  -> Adding as libFile");
									build_data.addLibFile(file_p);
								}
							}
						}
					} else {
						SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
								"Library Path directory \"" + stmt.getSrcLibPath() + "\" does not exist");
						m.setLocation(stmt.getLocation());
						markers.add(m);
					}
				} else if (ci.getType() == SVDBItemType.ArgFileSrcLibFileStmt) {
					SVDBArgFileSrcLibFileStmt stmt = (SVDBArgFileSrcLibFileStmt)ci;
					
					build_data.addLibFile(stmt.getSrcLibFile());
				}
			}

			// Save the markers, which might have been updated
			build_data.setMarkers(path, markers, true);
			build_data.setFileTree(path, ft, true);

			// Propagate markers to filesystem
// TODO:			propagateMarkers(path);
		} else {
			// Problem with root argument file
			// TODO: propagate markers
		}
	}

}
