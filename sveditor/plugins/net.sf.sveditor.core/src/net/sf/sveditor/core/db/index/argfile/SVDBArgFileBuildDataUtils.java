package net.sf.sveditor.core.db.index.argfile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
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
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache.FileType;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
import net.sf.sveditor.core.db.refs.SVDBFileRefFinder;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBArgFileBuildDataUtils implements ILogLevel {
	
	private static final LogHandle			fLog;
	private static boolean					fDebugEn;
	
	static {
		fLog = LogFactory.getLogHandle("SVDBArgFileBuildDataUtils");
	}

	/**
	 * Crawl through the file-tree structure 
	 * @param build_data
	 * @param ft
	 */
	public static void updateSrcFileAttr(
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
				build_data.setFileAttrBits(path, 
						ISVDBDeclCache.FILE_ATTR_HAS_MARKERS);
			}
		}
	}
	
	private static void updateSrcFileAttr(
			SVDBArgFileIndexBuildData	build_data,
			SVDBFileTree				ft) {
		if (ft.fMarkers != null && ft.fMarkers.size() > 0) {
			build_data.setFileAttrBits(ft.getFilePath(), 
					ISVDBDeclCache.FILE_ATTR_HAS_MARKERS);
		} else {
			build_data.clrFileAttrBits(ft.getFilePath(), 
					ISVDBDeclCache.FILE_ATTR_HAS_MARKERS);
		}
	
		for (SVDBFileTree ft_i : ft.fIncludedFileTrees) {
			updateSrcFileAttr(build_data, ft_i);
		}
	}

	/**
	 * Add the global declarations from the specified scope to the declaration
	 * cache
	 * 
	 * @param filename
	 * @param scope
	 */
	public static void cacheDeclarations(
			SVDBArgFileIndexBuildData	build_data,
			ISVDBDeclCache				parent,
			SVDBFile 					file, 
			SVDBFileTree 				ft) {
		fDebugEn = (fLog.getDebugLevel() > 0);
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
				parent,
				fileid, 
				file_item_list, 
				null, // pkg_item_list
				file,
				ft);

		if (ft != null) {
			cacheFileTreeDeclarations(ft, parent, file_item_list);
		}
	}
	
	private static void cacheFileDeclarations(
			SVDBArgFileIndexBuildData		build_data,
			ISVDBDeclCache					parent,
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
					decl_list.add(new SVDBDeclCacheItem(parent, 
							curr_filename, pkg.getName(), 
							item.getType(), false));
				}
				
				Map<String, List<SVDBDeclCacheItem>> pkg_map = 
						build_data.getPackageCacheMap();

				if (pkg_map.containsKey(pkg.getName())) {
					pkg_decl_l = pkg_map.get(pkg.getName());
				} else {
					pkg_decl_l = new ArrayList<SVDBDeclCacheItem>();
					pkg_map.put(pkg.getName(), pkg_decl_l);
				}
				pkg_decl_l.clear();
				
				cacheFileDeclarations(build_data, parent,
						curr_fileid, decl_list, pkg_decl_l, pkg, ft);
				
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
						decl_list.add(new SVDBDeclCacheItem(parent, curr_filename,
								((ISVDBNamedItem) item).getName(), item.getType(),
								false));
					}
				}
				if (pkg_decl_list != null) {
					fLog.debug(LEVEL_MID, "Adding " + item.getType() + " "
							+ ((ISVDBNamedItem) item).getName() + " to pkg_decl cache");
					pkg_decl_list.add(new SVDBDeclCacheItem(parent, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(),
							false));
				}
				
				// 'Global' declarations, such as classes, can be declared within Modules/Interfaces/Programs 
				// as well as packages. Scan through the top level of these elements
				if (item.getType().isElemOf(SVDBItemType.ModuleDecl, SVDBItemType.InterfaceDecl, SVDBItemType.ProgramDecl)) {
					cacheFileDeclarations(build_data, parent, curr_fileid, 
						decl_list, null, (ISVDBScopeItem)item, ft);
				}
			} else if (item.getType() == SVDBItemType.VarDeclStmt && is_root_scope) {
				SVDBVarDeclStmt decl = (SVDBVarDeclStmt) item;

				for (ISVDBChildItem ci : decl.getChildren()) {
					SVDBVarDeclItem di = (SVDBVarDeclItem) ci;
					fLog.debug(LEVEL_MID,
							"Adding var declaration: " + di.getName());

					if (decl_list != null) {
						decl_list.add(new SVDBDeclCacheItem(parent, curr_filename, 
								di.getName(), SVDBItemType.VarDeclItem, false));
					}
					if (pkg_decl_list != null) {
						pkg_decl_list.add(new SVDBDeclCacheItem(parent, curr_filename, 
								di.getName(), SVDBItemType.VarDeclItem, false));
					}
				}
			} else if (item.getType() == SVDBItemType.TypedefStmt && is_root_scope) {
				// Add entries for the typedef
				if (decl_list != null) {
					decl_list.add(new SVDBDeclCacheItem(parent, curr_filename,
							((ISVDBNamedItem) item).getName(), item.getType(), false));
				}
				
				if (pkg_decl_list != null) {
					pkg_decl_list.add(new SVDBDeclCacheItem(parent, curr_filename,
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
							decl_list.add(new SVDBDeclCacheItem(parent, curr_filename,
									((ISVDBNamedItem) en).getName(), 
									en.getType(), false));
						}
						if (pkg_decl_list != null) {
							pkg_decl_list.add(new SVDBDeclCacheItem(parent, curr_filename,
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

	private static void cacheFileTreeDeclarations(
			SVDBFileTree				ft,
			ISVDBDeclCache				parent,
			List<SVDBDeclCacheItem>		file_item_list) {
	
		if (ft.getSVDBFile() != null) {
			for (ISVDBChildItem c : ft.getSVDBFile().getChildren()) {
				if (c.getType() == SVDBItemType.MacroDef) {
					SVDBMacroDef def = (SVDBMacroDef)c;
					SVDBDeclCacheItem item = new SVDBDeclCacheItem(parent, 
							ft.getFilePath(),
							def.getName(),
							SVDBItemType.MacroDef,
							true);
					file_item_list.add(item);
				}
			}
		}
		
		for (SVDBFileTree ft_i : ft.getIncludedFileTreeList()) {
			cacheFileTreeDeclarations(ft_i, parent, file_item_list);
		}
	}

	public static void cacheReferences(SVDBArgFileIndexBuildData build_data, SVDBFile file) {
		Map<String, List<Integer>> ref_map = build_data.getReferenceCacheMap();
		
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
	
	/**
	 * Locate the argument file that includes the specified path
	 * 
	 * TODO: just brute forcing it for now
	 * 
	 * @param build_data
	 * @param path
	 * @return
	 */
	public static Tuple<SVDBFileTree, ISVDBItemBase> findContainingArgFile(
			SVDBArgFileIndexBuildData	build_data, 
			String						path,
			boolean						is_argfile) {
		Tuple<SVDBFileTree, ISVDBItemBase> ret = null;
		
		for (String af_path  : build_data.getFileList(ISVDBDeclCache.FILE_ATTR_ARG_FILE)) {
			SVDBFileTree af_ft = build_data.getCache().getFileTree(new NullProgressMonitor(), af_path, true);
			SVDBFile af_f = build_data.getCache().getFile(new NullProgressMonitor(), af_path);
			
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
	
	public static SVDBFileTree findTargetFileTree(
			SVDBArgFileIndexBuildData 	build_data, 
			String 						path) {
		ISVDBFileSystemProvider	fs_provider = build_data.getFSProvider();
		SVDBFileTree ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fs_provider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fs_provider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
	
		// TODO: probably want to change this somehow
		synchronized (build_data) {
			if (build_data.containsFile(path, ISVDBDeclCache.FILE_ATTR_ARG_FILE)) {
				// This is an argfile path
				ret = build_data.getCache().getFileTree(new NullProgressMonitor(), path, true);
			} else {
				boolean is_root = false;
				Map<String, List<String>> inc_map = build_data.getRootIncludeMap();
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
					SVDBFileTree ft = build_data.getCache().getFileTree(
							new NullProgressMonitor(), root, false);
					if (ft != null) {
						if (is_root) {
							ret = ft;
						} else {
							ret = SVDBFileTreeUtils.findTargetFileTree(ft, paths);
						}
					} else {
						fLog.error("Failed to obtain FileTree " + root + " from cache");
					}
				}
			}
		
			/*
			// Search the file tree of each root file
			Set<String> file_list = build_data.getCache().getFileList(false);
//			System.out.println("file_list: " + file_list.size());
			for (String root_path : file_list) {
				long start = System.currentTimeMillis();
				SVDBFileTree ft = build_data.getCache().getFileTree(
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

	public static SVDBFileTree findRootFileTree(SVDBArgFileIndexBuildData build_data, String path) {
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		SVDBFileTree ret = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fs_provider.resolvePath(path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			if (!fs_provider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
		}
	
		// TODO: probably want to check the search procedure somehow
		synchronized (build_data) {
			String root = null;
			Map<String, List<String>> inc_map = build_data.getRootIncludeMap();
			for (Entry<String, List<String>> e : inc_map.entrySet()) {
				if (e.getKey().equals(path) || e.getValue().contains(path)) {
					root = e.getKey();
					break;
				}
			}
			
			if (root != null) {
				ret = build_data.getCache().getFileTree(
						new NullProgressMonitor(), root, false);
			}
		}

		return ret;
	}

	// TODO: encapsulation here seems suspect
	public static String findRootFilePath(SVDBArgFileIndexBuildData build_data, String path) {
		String ret = null;
		
		synchronized (build_data) {
			Map<String, List<String>> root_map = build_data.getRootIncludeMap();
			
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

	/**
	 * Locates markers for the specified file and adds them to the list
	 * 
	 * @param markers
	 * @param r_path
	 */
	public static void findFileMarkers(
			SVDBArgFileIndexBuildData		build_data,
			List<SVDBMarker> 				markers, 
			String 							r_path) {
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		List<SVDBMarker>	root_markers = null;
		int 				file_id = -1;
		SVDBFileTree 		target_ft = null;
		String paths[] = new String[3];
		String fmts[] = {null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM };

		for (int fmt_idx=0; fmt_idx<fmts.length; fmt_idx++) {
			paths[fmt_idx] = fs_provider.resolvePath(r_path, fmts[fmt_idx]);
		
			// Null out, since we don't need to check
			/*
			if (!fFileSystemProvider.fileExists(paths[fmt_idx])) {
				paths[fmt_idx] = null;
			}
			 */
		}
		
		String root_file = findRootFilePath(build_data, r_path);

		if (root_file != null) {
			SVDBFileTree ft = build_data.getCache().getFileTree(
					new NullProgressMonitor(), root_file, false);

			if (ft != null) {
				target_ft = SVDBFileTreeUtils.findTargetFileTree(ft, r_path);
				file_id = build_data.mapFilePathToId(r_path, false);
				root_markers = build_data.getCache().getMarkers(root_file);
			}
		}

		// Search the file tree of each root file
		/*
			for (String root_path : fBuildData.getCache().getFileList(false)) {
				SVDBFileTree ft = fBuildData.getCache().getFileTree(
						new NullProgressMonitor(), root_path, false);
				if ((target_ft = findTargetFileTree(ft, paths)) != null) {
					file_id = fBuildData.mapFilePathToId(root_path, false);
					root_markers = fBuildData.getCache().getMarkers(root_path);
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
	
	/**
	 * Traverse through the FileTree structure to calculate the
	 * macros defined prior to parse of a specific file. This
	 * method is only used by the parse() method used to parse
	 * content in the context of indexed content
	 * 
	 * @param ft
	 * @return
	 */
	public static List<SVDBMacroDef> calculateIncomingMacros(
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
			SVDBFileTreeUtils.collectRootFileTreeMacros(all_defs, ft);
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
							SVDBFileTreeUtils.collectRootFileTreeMacros(all_defs, inc_ft);
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

	public static void createSubFileMap(
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
	
	public static List<SVDBDeclCacheItem> findGlobalScopeDecl(
			SVDBArgFileIndexBuildData		build_data,
			IProgressMonitor				monitor,
			String							name,
			ISVDBFindNameMatcher			matcher) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		
		Map<String, List<SVDBDeclCacheItem>> decl_cache = build_data.getDeclCacheMap();

		for (Entry<String, List<SVDBDeclCacheItem>> e : decl_cache.entrySet()) {
			for (SVDBDeclCacheItem item : e.getValue()) {
				if (matcher.match(item, name)) {
					ret.add(item);
				}
			}
		}

		return ret;		
	}
	
	public static SVDBFile findFile(
			SVDBArgFileIndexBuildData			build_data,
			IProgressMonitor					monitor,
			String								path) {
		String r_path = path;
		SVDBFile ret = null;
		
		if (fDebugEn) {
			fLog.debug("--> findFile: " + path);
		}
		
		ISVDBIndexCache.FileType ft = build_data.getCache().getFileType(r_path);
		
		if (ft == FileType.ArgFile) {
			// Just return the file
			ret = build_data.getCache().getFile(new NullProgressMonitor(), r_path);
		} else {
			// We assume the file is SystemVerilog
			int id = build_data.mapFilePathToId(r_path, false);
			
			// See if we can find the root file
			String root_path = findRootFilePath(build_data, r_path);
			int root_id = build_data.mapFilePathToId(root_path, false);
			
			if (root_path != null) {
				// Get the FileMap
				Map<Integer, SVDBFile> map = build_data.getCache().getSubFileMap(root_path);
				
				if (map == null) {
					// re-create the map
					SVDBFile file = build_data.getCache().getFile(new NullProgressMonitor(), root_path);
					
					if (file != null) {
						map = new HashMap<Integer, SVDBFile>();

						SVDBFile f = new SVDBFile(root_path);
						f.setLocation(SVDBLocation.pack(root_id, -1, -1));
						map.put(root_id, f);
						//					long start = System.currentTimeMillis();
						createSubFileMap(build_data, map, file, root_id, f);
						//					long end = System.currentTimeMillis();
						build_data.getCache().setSubFileMap(root_path, map);
						
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
	
	public static List<SVDBDeclCacheItem> findPackageDecl(
			SVDBArgFileIndexBuildData			build_data,
			IProgressMonitor					monitor,
			SVDBDeclCacheItem					pkg_item) {
		List<SVDBDeclCacheItem> ret = new ArrayList<SVDBDeclCacheItem>();
		Map<String, List<SVDBDeclCacheItem>> pkg_cache = 
				build_data.getPackageCacheMap();

		List<SVDBDeclCacheItem> pkg_content = pkg_cache.get(pkg_item.getName());

		if (pkg_content != null) {
			ret.addAll(pkg_content);
		}

		return ret;		
	}
	
	public static List<SVDBMarker> getMarkers(
			SVDBArgFileIndexBuildData			build_data,
			IProgressMonitor					monitor,
			String								path) {
		if (fDebugEn) {
			fLog.debug("-> getMarkers: " + path);
		}
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		// TODO: Doesn't consider that root file isn't necessarily what we're after
		boolean is_argfile = false;
		String r_path = path;
	
		is_argfile = build_data.containsFile(path, 
				ISVDBDeclCache.FILE_ATTR_ARG_FILE);

		if (is_argfile) {
			markers.addAll(build_data.getCache().getMarkers(r_path));
		} else {
			findFileMarkers(build_data, markers, path);
		}
			
		if (fDebugEn) {
			fLog.debug("<- getMarkers: " + path + ": " + markers.size());
		}

		return markers;		
	}
}
