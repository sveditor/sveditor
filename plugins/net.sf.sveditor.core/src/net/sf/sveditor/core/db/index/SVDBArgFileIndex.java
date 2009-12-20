package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
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
	public void load(IDBReader index_data, List<SVDBFile> ppFiles,
			List<SVDBFile> dbFiles) {
		try {
			fArgFileLastModified = index_data.readLong();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		super.load(index_data, ppFiles, dbFiles);
	}

	@Override
	protected boolean isLoadUpToDate() {
		return (fFileSystemProvider.fileExists(getResolvedBaseLocation()) &&
				fArgFileLastModified >= fFileSystemProvider.getLastModifiedTime(getResolvedBaseLocation()) &&
				super.isLoadUpToDate());
	}
	
	@Override
	public void fileChanged(String path) {
		System.out.println("fileChanged: \"" + path + "\"");
		if (path.equals(getResolvedBaseLocation())) {
			fFileIndexValid = false;
			fFileListValid  = false;
		} else {
			super.fileChanged(path);
		}
	}

	@Override
	protected void buildPreProcFileMap() {
		InputStream in = fFileSystemProvider.openStream(getResolvedBaseLocation());
		
		if (in != null) {
			ITextScanner sc = new InputStreamTextScanner(in, getResolvedBaseLocation());
			SVFScanner scanner = new SVFScanner();
			
			try {
				scanner.scan(sc);
			} catch (Exception e) {
				e.printStackTrace();
			}
			
			for (String f : scanner.getFilePaths()) {
				System.out.println("[FILE PATH] " + f);
				fFilePaths.add(expandVars(f, true));
			}
			
			for (String inc : scanner.getIncludePaths()) {
				System.out.println("[INC PATH] " + inc + " (" + expandVars(inc, true) + ")");
				fIncludePaths.add(expandVars(inc, true));
			}
			
		} else {
			System.out.println("[ERROR] failed to open file \"" + getResolvedBaseLocation() + "\"");
		}
		
		// Say the index is already valid
		fFileListValid = true;
		
		for (String file : fFilePaths) {
			file = resolvePath(file);
			SVDBFile pp_file = processPreProcFile(file);
			
			if (pp_file == null) {
				System.out.println("Failed to find file \"" + file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}
	}
	
	@Override
	protected void buildIndex() {
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		getPreProcFileMap(); // force pre-proc info to be built

		for (String file : fFilePaths) {
			file = resolvePath(file);
			SVDBFile pp_file = findPreProcFile(file);
			
			if (pp_file == null) {
				System.out.println("Failed to find file \"" + file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = fFileTreeMap.get(file);
			
			processFile(ft_root, dp);
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
			return getResolvedBaseLocationDir() + "/" + path;
		} else if (path.startsWith(".")) {
			if (path.equals(".")) {
				return getResolvedBaseLocationDir();
			} else { 
				return getResolvedBaseLocationDir() + "/" + path.substring(2);
			}
		} else {
			return path;
		}
	}

}
