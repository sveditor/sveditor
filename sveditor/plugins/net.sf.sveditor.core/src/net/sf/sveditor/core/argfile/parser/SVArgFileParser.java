package net.sf.sveditor.core.argfile.parser;

import java.io.File;
import java.io.IOException;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.argfile.parser.ISVArgFileOptionProvider.OptionType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

public class SVArgFileParser {
	private SVArgFileOptionProviderList			fOptionProviders;
	private SVArgFileLexer						fLexer;
	private String								fFilename;
	private LogHandle							fLog;
	private boolean							fDebugEn = true;
	private List<SVDBMarker>					fMarkers;
	private ISVDBFileSystemProvider				fFSProvider;
	private String								fResolvedBaseLocation;
	private String								fBaseLocation;
	
	public SVArgFileParser(
			String						base_location,
			String 						resolved_base_location, 
			ISVDBFileSystemProvider 	fs_provider) {
		fOptionProviders = new SVArgFileOptionProviderList();
		fOptionProviders.add(new SVArgFileQuestaOptionProvider());
		fOptionProviders.add(new SVArgFileVCSOptionProvider());
		fOptionProviders.add(new SVArgFileNCVlogOptionProvider());
		
		fLog = LogFactory.getLogHandle("SVArgFileParser");
		fResolvedBaseLocation = resolved_base_location;
		fBaseLocation = base_location;
		fFSProvider = fs_provider;
	}
	
	public void init(SVArgFileLexer lexer, String name) {
		fLexer = lexer;
		fFilename = name;
	}
	
	public SVDBFile parse(
			SVDBFile			file,
			List<SVDBMarker> 	markers) throws SVParseException {
		
		fMarkers = markers;
	
		if (fDebugEn) {
			fLog.debug("--> parse() " + fFilename);
		}
		
		while (fLexer.peek() != null) {
			if (fLexer.isOption()) {
				SVArgFileToken tok = fLexer.consumeToken();
				OptionType type = fOptionProviders.getOptionType(tok.getImage());
				int arg_count = fOptionProviders.optionArgCount(tok.getImage());
				
				if (fDebugEn) {
					fLog.debug("  isOption: " + tok.getImage() + " type=" + type + 
							" arg_count=" + arg_count);
				}
				
				// Determine what type of option this is
				switch (type) {
					case Unrecognized: {
						// TODO: Treat as a single-item option and ignore
						fLexer.eatToken();
						} break;
					
						// Recognized, but ignored, option
					case Ignored: {
						// TODO: Consume known options
						for (int i=0; i<arg_count; i++) {
							fLexer.eatToken();
						}
						} break;
						
					case Incdir: {
						SVDBArgFileIncDirStmt stmt = new SVDBArgFileIncDirStmt();
						stmt.setLocation(fLexer.getStartLocation());
						String path;
						
						if (arg_count > 0) {
							// include path is the argument
							path = fLexer.readPath();
							List<String> inc_path_l = fOptionProviders.getIncPaths(tok.getImage(), path);
							path = inc_path_l.get(0);
						} else {
							List<String> inc_path_l = fOptionProviders.getIncPaths(
									tok.getImage(), 
									tok.getOptionVal());
							path = inc_path_l.get(0);
						}

						if (path != null) {
							path = resolvePath(path);

							if (!fFSProvider.fileExists(path)) {
								error(tok.getStartLocation(), "Include path \"" + path + "\" does not exist. " +
										"Resolved relative to \"" + fResolvedBaseLocation + "\"");

							}
							stmt.setIncludePath(path);
						} else {
							error(tok.getStartLocation(), "No include-file path provided");
							stmt.setIncludePath("");
						}
						
						file.addChildItem(stmt);
						} break;
						
					case Define: {
						SVDBArgFileDefineStmt stmt = new SVDBArgFileDefineStmt();
						stmt.setLocation(fLexer.getStartLocation());
						Tuple<String, String> def;
						
						if  (arg_count > 0) {
							// Define is the argument
							def = fOptionProviders.getDefValue(
									tok.getImage(),
									fLexer.readPath());
						} else {
							def = fOptionProviders.getDefValue(
									tok.getImage(),
									tok.getOptionVal());
						}
						
						stmt.setKey(def.first());
						stmt.setValue(def.second());
						
						file.addChildItem(stmt);
						} break;
						
					case ArgFileInc: {
						SVDBArgFileIncFileStmt stmt = new SVDBArgFileIncFileStmt();
						stmt.setLocation(tok.getStartLocation());
						List<String> incs;
						
						if (arg_count > 0) {
							incs = fOptionProviders.getArgFilePaths(
									tok.getImage(), fLexer.readPath());
						} else {
							incs = fOptionProviders.getArgFilePaths(
									tok.getImage(),
									tok.getOptionVal());
						}
						
						if (incs == null || incs.size() == 0) {
							error(tok.getStartLocation(), "No argument-file path provided");
						} else {
							String inc = incs.get(0);
							
							if (inc != null) {
								String path = resolvePath(incs.get(0));
								if (!fFSProvider.fileExists(path)) {
									error(tok.getStartLocation(), 
											"Argument-file path \"" + path + "\" does not exist; " +
													"Resolved relative to \"" + fResolvedBaseLocation + "\"");
								}
								stmt.setPath(path);
							} else {
								error(tok.getStartLocation(), "No argument-file path provided");
								stmt.setPath("");
							}
							file.addChildItem(stmt);
						}
						} break;
						
					case SrcLibPath: {
						SVDBArgFileSrcLibPathStmt stmt = new SVDBArgFileSrcLibPathStmt();
						stmt.setLocation(fLexer.getStartLocation());
						
						String path = fLexer.readPath();
						path = resolvePath(path);
						if (!fFSProvider.isDir(path)) {
							error(tok.getStartLocation(),
									"Source library path \"" + path + "\" does not exist; " + 
										"Resolved relative to \"" + fResolvedBaseLocation + "\"");
						}
						stmt.setSrcLibPath(path);
						file.addChildItem(stmt);
						} break;
						
					default:
						error(tok.getStartLocation(), "Unrecognized option type " + type);
						break;
				}
			} else {
				// It's a path
				SVDBArgFilePathStmt p = new SVDBArgFilePathStmt();
				SVDBLocation loc = fLexer.getStartLocation();
				p.setLocation(loc);
				String path = fLexer.eatToken();
				file.addChildItem(p);
				
				// Try to resolve path
				path = resolvePath(path);
				p.setPath(path);
				
				if (!fFSProvider.fileExists(path)) {
					error(loc, "Path \"" + path + "\" does not exist; " + 
						"Resolved relative to \"" + fResolvedBaseLocation + "\"");
				}
			}
		}
		
		fLog.debug("<-- parse() " + fFilename);
		
		return file;
	}
	
	private String resolvePath(String path) {
		/*
		for (String fmt : new String[] { null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM}) {
			String rpath = fFSProvider.resolvePath(path, fmt);
			
			if (fFSProvider.fileExists(rpath)) {
				path = rpath;
				break;
			}
		}
	
		return path;
		 */
		return resolvePath(path, true);
	}
	
	protected String resolvePath(String path_orig, boolean in_workspace_ok) {
		String path = path_orig;
		String norm_path = null;

		if (fDebugEn) {
			fLog.debug("--> resolvePath: " + path_orig);
		}

		// relative to the base location or one of the include paths
		if (path.startsWith("..")) {
			if (fDebugEn) {
				fLog.debug("    path starts with ..");
			}
			if ((norm_path = resolveRelativePath(fResolvedBaseLocation, path)) == null) {
				/*
				for (String inc_path : fIndexCacheData.getIncludePaths()) {
					if (fDebugEn) {
						fLog.debug("    Check: " + inc_path + " ; " + path);
					}
					if ((norm_path = resolveRelativePath(inc_path, path)) != null) {
						break;
					}
				}
				 */
			} else {
				if (fDebugEn) {
					fLog.debug("norm_path=" + norm_path);
				}
			}
		} else {
			if (path.equals(".")) {
				path = fResolvedBaseLocation;
			} else if (path.startsWith(".")) {
				path = fResolvedBaseLocation + "/" + path.substring(2);
			} else {
				if (!fFSProvider.fileExists(path)) {
					// See if this is an implicit path
					String imp_path = fResolvedBaseLocation + "/" + path;

					if (fFSProvider.fileExists(imp_path)) {
						// This path is an implicit relative path that is
						// relative to the base directory
						path = imp_path;
					}
				}
			}
			norm_path = normalizePath(path);
		}
		
		if (norm_path != null && !norm_path.startsWith("${workspace_loc}") && in_workspace_ok) {
			IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = ws_root.getFileForLocation(new Path(norm_path));
			if (file != null && file.exists()) {
				norm_path = "${workspace_loc}" + file.getFullPath().toOSString();
			} else {
				IContainer folder = ws_root.getContainerForLocation(new Path(norm_path));
				if (folder != null && folder.exists()) {
					norm_path = "${workspace_loc}" + folder.getFullPath().toOSString();
				}
			}
		}
		
		norm_path = (norm_path != null) ? norm_path : path_orig;
		
		if (fDebugEn) {
			fLog.debug("<-- resolvePath: " + path_orig + " " + norm_path);
		}

		return norm_path;
	}

	private String resolveRelativePath(String base, String path) {
		String ret = null;
		if (fDebugEn) {
			fLog.debug("--> resolveRelativePath: base=" + base + " path=" + path);
		}
		
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base + "/" + path);

		if (fDebugEn) {
			fLog.debug("    Checking normalizedPath: " + norm_path
					+ " ; ResolvedBaseLocation: " + fResolvedBaseLocation);
		}

		if (fFSProvider.fileExists(norm_path)) {
			ret = norm_path;
		} else if (fBaseLocation.startsWith("${workspace_loc}")) {
			// This could be a reference outside the workspace. Check
			// whether we should reference this as a filesystem path
			// by computing the absolute path
			String base_loc = fResolvedBaseLocation;
			if (fDebugEn) {
				fLog.debug("Possible outside-workspace path: " + base_loc);
			}
			base_loc = base_loc.substring("${workspace_loc}".length());

			if (fDebugEn) {
				fLog.debug("    base_loc: " + base_loc);
			}

			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer base_dir = null;
			try {
				base_dir = root.getFolder(new Path(base_loc));
			} catch (IllegalArgumentException e) {
			}

			if (base_dir == null) {
				if (base_loc.length() > 0) {
					base_dir = root.getProject(base_loc.substring(1));
				}
			}

			if (fDebugEn) {
				fLog.debug("base_dir=" + ((base_dir != null)?base_dir.getFullPath().toOSString():null));
			}

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					if (fDebugEn) {
						fLog.debug("Location of base_dir: " + base_dir_p.toOSString());
					}
					File path_f_t = new File(base_dir_p.toFile(), path);
					if (fDebugEn) {
						fLog.debug("Checking if path exists: " + path_f_t.getAbsolutePath() + " " + path_f_t.exists());
					}
					try {
						if (path_f_t.exists()) {
							if (fDebugEn) {
								fLog.debug("Path does exist outside the project: "
										+ path_f_t.getCanonicalPath());
							}
							norm_path = SVFileUtils.normalize(path_f_t
									.getCanonicalPath());
							ret = norm_path;
						}
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- resolveRelativePath: base=" + base + " path=" + path + " ret=" + ret);
		}
		return ret;
	}

	protected String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();

		int i = path.length() - 1;
		int end;
		int skipCnt = 0;

		// First, skip any trailing '/'
		while (i >= 0 && (path.charAt(i) == '/' || path.charAt(i) == '\\')) {
			i--;
		}

		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();

			while (i >= 0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}

			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length() - 1);
				if (str.equals("..")) {
					skipCnt++;
					// remove .. element
					ret.setLength(end);
				} else if (skipCnt > 0) {
					ret.setLength(end);
					skipCnt--;
				}
			}
		}

		return ret.reverse().toString();
	}	
	
	private void error(SVDBLocation location, String msg) throws SVParseException {
		if (fMarkers != null) {
			SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.UndefinedMacro, msg);
			m.setLocation(location);
			fMarkers.add(m);
		}
//		System.out.println("[ERROR] " + msg);
	}
}
