package net.sf.sveditor.core.db.index.argfile;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import net.sf.sveditor.core.builder.ISVBuilderOutput;
import net.sf.sveditor.core.builder.SVBuilderPreProcTracker;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ISVTokenListener;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.parser.SVToken;
import net.sf.sveditor.core.preproc.SVPreProcFileTreeBuilder;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;

public class SVDBArgFileBuildUtils implements ILogLevel {
	private static boolean				fDebugEn;
	private static final LogHandle		fLog;
	private static final ILogLevelListener fLogLevelListener = new ILogLevelListener() {
		
		@Override
		public void logLevelChanged(ILogHandle handle) {
			fDebugEn = (handle.getDebugLevel() > 0);
		}
	};
	
	static {
		fLog = LogFactory.getLogHandle("SVDBArgFileBuildUtils");
		fLog.addLogLevelListener(fLogLevelListener);
		fLogLevelListener.logLevelChanged(fLog);
	}
	
	public static void buildIndex(
			IProgressMonitor			monitor,
			SVDBArgFileIndexBuildData	build_data,
			ISVDBDeclCache				parent,
			SVDBArgFileParser			argfile_parser,
			ISVBuilderOutput			out) {
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		long start_time=-1, end_time=-1;
		int total_work = 1000000;
		int per_file_work = 0;
		fDebugEn = (fLog.getDebugLevel() > 0);
		
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Build Index", total_work);

		// First, parse the argument files
		start_time = System.currentTimeMillis();
		
		argfile_parser.discoverRootFiles(subMonitor.newChild(100), build_data);
		if (fDebugEn) {
			end_time = System.currentTimeMillis();
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + build_data.getBaseLocation()
					+ ": Parse argument files -- " + (end_time - start_time)
					+ "ms");
		}

		if (subMonitor.isCanceled()) {
			fLog.debug(LEVEL_MIN, "Index " + build_data.getBaseLocation() + " cancelled");
			return;
		}

		// Next, parse each of the discovered file paths
		List<String> paths = build_data.getFileList(
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_ROOT_FILE);
		List<String> libfile_paths = build_data.getFileList(
				ISVDBDeclCache.FILE_ATTR_SRC_FILE+
				ISVDBDeclCache.FILE_ATTR_LIB_FILE);
		Map<String, SVDBMacroDef> defines = new HashMap<String, SVDBMacroDef>();
		
		build_data.getIndexStats().setNumRootFiles(paths.size());
		
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
			
			if (fs_provider.fileExists(path) && !fs_provider.isDir(path)) {
				subMonitor.subTask("Parse " + path);
				out.note("Parse: " + path);
				
				Map<String, SVDBMacroDef> new_defines = parseFile(
						path, build_data, parent, defines, out);
				
				if (subMonitor.isCanceled()) {
					fLog.debug(LEVEL_MIN, "Index " + build_data.getBaseLocation() + " cancelled");
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

				subMonitor.worked(per_file_work);
			} else {
				out.error("File " + path + " doesn't exist");
			}
		}
		
		// Finally, parse library-file paths
		for (int i=0; i<libfile_paths.size(); i++) {
			String path = libfile_paths.get(i);
			
			if (fDebugEn) {
				fLog.debug(LEVEL_MID, "LibFile Path: " + path);
			}
			
			if (fs_provider.fileExists(path) && !fs_provider.isDir(path)) {
				SubMonitor loopMonitor = subMonitor.newChild(per_file_work);
				loopMonitor.beginTask("Parse " + path, per_file_work);
				
				Map<String, SVDBMacroDef> new_defines = parseFile(
						path, build_data, parent, defines, out);
				
				if (loopMonitor.isCanceled()) {
					fLog.debug(LEVEL_MIN, "Index " + 
							build_data.getBaseLocation() + " cancelled");
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

				loopMonitor.worked(per_file_work);
			}			
		}

		// End of the total index
		end_time = System.currentTimeMillis();
		
		build_data.getIndexStats().incLastIndexTotalTime(end_time-start_time);
		
//		Map<String, List<Integer>> refMap = build_data.fRefCollector.getRefMap();
//		for (Entry<String, List<Integer>> ent : refMap.entrySet()) {
//			System.out.print(ent.getKey() + ": ");
//			for (Integer file : ent.getValue()) {
//				System.out.print(file + " ");
//			}
//			System.out.println();
//		}
	
		if (fDebugEn) {
			fLog.debug(LEVEL_MIN, "Index " + build_data.getBaseLocation()
					+ ": Parse source files -- " + (end_time - start_time)
					+ "ms");
		}
		
		subMonitor.done();
	}

	public static Map<String, SVDBMacroDef> parseFile(
			String 								path, 
			final SVDBArgFileIndexBuildData 	build_data,
			ISVDBDeclCache						parent,
			Map<String, SVDBMacroDef>			defines,
			final ISVBuilderOutput				out) {
		ISVDBFileSystemProvider fs_provider = build_data.getFSProvider();
		long start, end;
		SVParser f = new SVParser();
		f.setFileMapper(build_data);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

		InputStream in = fs_provider.openStream(path);

		start = System.currentTimeMillis();
		
		// Propagate defines to the pre-processor
		SVPreProcessor pp = new SVPreProcessor(path, in, build_data, build_data);
		SVPreProcFileTreeBuilder ft_builder = new SVPreProcFileTreeBuilder();
		pp.addListener(ft_builder);
		pp.setIndexStats(build_data.getIndexStats());

		// Pass in defines
		for (Entry<String, SVDBMacroDef> def : defines.entrySet()) {
			pp.setMacro(def.getValue());
		}

		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "--> PreProcess " + path);
		}
		SVPreProcOutput pp_out = pp.preprocess();
		pp_out.setFileChangeListener(new SVBuilderPreProcTracker(out, build_data));
		end = System.currentTimeMillis();
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "<-- PreProcess " + path + ": " +
					(end-start) + "ms");
		}
		
		SVDBFileTree ft = ft_builder.getFileTree();
		
		// Add a mapping between root file and included files
		List<String> included_files = new ArrayList<String>();
		SVDBFileTreeUtils.collectIncludedFiles(included_files, ft);
	
		// TODO: encapsulation seems odd here
		build_data.getRootIncludeMap().remove(path);
		build_data.getRootIncludeMap().put(path, included_files);

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
		
		final Set<String> ident_set = new HashSet<String>();
		ISVTokenListener tok_listener = new ISVTokenListener() {
			
			@Override
			public void ungetToken(SVToken tok) { }
			
			@Override
			public void tokenConsumed(SVToken tok) {
				if (tok.isIdentifier()) {
					ident_set.add(tok.getImage());
				}
			}
		};
		
		SVDBFile file = f.parse(language_level, pp_out, path, tok_listener, markers);
		long parse_end = System.currentTimeMillis();
		
		build_data.getIndexStats().incLastIndexParseTime(parse_end-parse_start);
		
		if (fDebugEn) {
			fLog.debug(LEVEL_MID, "<-- Parse " + path + ": " +
					(parse_end-parse_start) + "ms");
		}

		start = System.currentTimeMillis();
		SVDBArgFileBuildDataUtils.cacheDeclarations(build_data, parent, file, ft);
		end = System.currentTimeMillis();
		build_data.getIndexStats().incLastIndexDeclCacheTime(end-start);
		
		start = System.currentTimeMillis();
		SVDBArgFileBuildDataUtils.cacheReferences(build_data, file);
		end = System.currentTimeMillis();
		build_data.getIndexStats().incLastIndexRefCacheTime(end-start);
		
		start = System.currentTimeMillis();
		long last_modified = fs_provider.getLastModifiedTime(path);
		build_data.getCache().setFile(path, file, false);
		build_data.getCache().setFileTree(path, ft, false);
		build_data.getCache().setMarkers(path, markers, false);
		build_data.getCache().setLastModified(path, last_modified, false);
		
		// Update source file attributes
		SVDBArgFileBuildDataUtils.updateSrcFileAttr(build_data, ft, markers);

		end = System.currentTimeMillis();

		if (build_data.isMFCU()) {
			// In MFCU mode, collect the defined macros and 
			// return them
			Map<String, SVDBMacroDef> defined_macros = new HashMap<String, SVDBMacroDef>();
			SVDBFileTreeUtils.collectFileTreeMacros(defined_macros, ft);
			
			return defined_macros;
		} else {
			return null;
		}
	}
}
