package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.SVFileTreeMacroProvider;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

public class SVDBArgFileIndex extends SVDBLibIndex {
	private String						fBaseLocationDir;
	private long						fArgFileLastModified;
	protected List<String>				fFilePaths;
	protected List<String>				fIncludePaths;
	protected Map<String, String>		fDefineMap;
	
	
	public SVDBArgFileIndex(
			String						project,
			String						root,
			ISVDBFileSystemProvider		fs_provider) {
		super(project, root, fs_provider);
		fLog = LogFactory.getDefault().getLogHandle("SVDBArgFileIndex");
		
		fFilePaths = new ArrayList<String>();
		fIncludePaths = new ArrayList<String>();
		fDefineMap = new HashMap<String, String>();
	}
	
	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}
	
	private String getResolvedBaseLocationDir() {
		if (fBaseLocationDir == null) {
			fBaseLocationDir = new File(getResolvedBaseLocation()).getParent();
		}
		return fBaseLocationDir;
	}

	@Override
	public void dump(IDBWriter index_data) {
		// Save the last-modified time for the arg file
		long last_modified = fFileSystemProvider.getLastModifiedTime(getResolvedBaseLocation());
		index_data.writeLong(last_modified);
		
		super.dump(index_data);
	}

	@Override
	public void load(
			IDBReader 		index_data, 
			List<SVDBFile> 	pp_files,
			List<SVDBFile> 	db_files) throws DBFormatException {
		fArgFileLastModified = index_data.readLong();
		
		load_base(index_data, pp_files, db_files);
		
		if (isLoaded()) {
			readArgFile();

			// re-build the FileTree structure
			for (String file : fFilePaths) {
				file = resolvePath(file);
				SVDBFile pp_file = findPreProcFile(file);
				
				if (pp_file == null) {
					fLog.error("Failed to find file \"" + file + "\"");
					continue;
				}
				
				SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
				buildPreProcFileMap(null, ft_root);
			}
		}
	}

	@Override
	protected boolean isLoadUpToDate() {
		return (fFileSystemProvider.fileExists(getResolvedBaseLocation()) &&
				fArgFileLastModified >= fFileSystemProvider.getLastModifiedTime(getResolvedBaseLocation()) &&
				super.isLoadUpToDate());
	}
	
	@Override
	public void fileChanged(String path) {
		if (path.equals(getResolvedBaseLocation())) {
			fFileIndexValid = false;
			fFileListValid  = false;
		} else {
			super.fileChanged(path);
		}
	}

	@Override
	protected void buildPreProcFileMap() {
		readArgFile();
		
		// Say the index is already valid
		fFileListValid = true;
		
		for (String file : fFilePaths) {
			String r_file = resolvePath(file);
			fLog.debug("Resolved path for \"" + file + "\" is \"" + r_file + "\"");
			SVDBFile pp_file = processPreProcFile(r_file);
			
			if (pp_file == null) {
				fLog.error("Failed to find file \"" + r_file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}
	}
	
	protected void readArgFile() {
		fFilePaths.clear();
		fIncludePaths.clear();
		
		InputStream in = fFileSystemProvider.openStream(getResolvedBaseLocation());
		
		if (in != null) {
			ITextScanner sc = new InputStreamTextScanner(in, getResolvedBaseLocation());
			SVFScanner scanner = new SVFScanner();
			
			try {
				scanner.scan(sc);
			} catch (Exception e) {
				fLog.error("Failed to read argument file \"" + 
						getResolvedBaseLocation() + "\"", e);
			}
			
			for (String f : scanner.getFilePaths()) {
				fLog.debug("[FILE PATH] " + f);
				fFilePaths.add(expandVars(f, true));
			}
			
			for (String inc : scanner.getIncludePaths()) {
				fLog.debug("[INC PATH] " + inc + " (" + expandVars(inc, true) + ")");
				fIncludePaths.add(expandVars(inc, true));
			}
			
		} else {
			fLog.error("failed to open file \"" + getResolvedBaseLocation() + "\"");
		}
	}
	
	@Override
	protected void buildIndex() {
		getPreProcFileMap(); // force pre-proc info to be built

		for (String file : fFilePaths) {
			file = resolvePath(file);
			SVDBFile pp_file = findPreProcFile(file);
			
			if (pp_file == null) {
				fLog.error("Failed to find file \"" + file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = fFileTreeMap.get(file);
			SVFileTreeMacroProvider mp = new SVFileTreeMacroProvider(ft_root);
			
			processFile(ft_root, mp);
		}
		
		fFileIndexValid = true;
	}
	
	@Override
	public SVDBSearchResult<SVDBFile> findIncludedFile(String path) {
		SVDBSearchResult<SVDBFile> ret = null;
		
		if ((ret = super.findIncludedFile(path)) != null) {
			return ret;
		}
		
		// Otherwise, search through each include path
		for (String inc : fIncludePaths) {
			inc = resolvePath(inc);
			inc = inc + "/" + path;
			
			if (fFileSystemProvider.fileExists(inc)) {
				SVDBFile pp_file = processPreProcFile(inc);
				
				ret = new SVDBSearchResult<SVDBFile>(pp_file, this);
			}
		}
		
		return ret;
	}

	protected String resolvePath(String path) {
		
		// relative to the base location
		if (path.startsWith("..")) {
			path = getResolvedBaseLocationDir() + "/" + path;
		} else if (path.startsWith(".") || Character.isJavaIdentifierStart(path.charAt(0))) {
			if (path.equals(".")) {
				path = getResolvedBaseLocationDir();
			} else if (path.startsWith(".")) { 
				path = getResolvedBaseLocationDir() + "/" + path.substring(2);
			} else {
				// This path is an implicit relative path that is 
				// relative to the base directory
				path = getResolvedBaseLocationDir() + "/" + path;
			}
		}
		
		String norm_path = normalizePath(path);
		
		return norm_path;
	}
	
	protected String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();
		
		int i=path.length()-1;
		int end;
		int skipCnt = 0;
		
		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();
			
			while (i>=0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}
			
			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length()-1);
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
		
		if (skipCnt > 0) {
			throw new RuntimeException("exceeded skipCnt");
		}
		
		return ret.reverse().toString();
	}

}
