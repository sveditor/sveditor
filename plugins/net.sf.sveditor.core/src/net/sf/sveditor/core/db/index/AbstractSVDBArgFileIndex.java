package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

public abstract class AbstractSVDBArgFileIndex extends AbstractSVDBIndex {
	
	protected String						fArgFile;
	protected String						fBaseDir;
	protected List<String>					fFilePaths;
	protected List<String>					fIncludePaths;
	protected Map<String, String>			fDefineMap;
	protected Map<String, SVDBFileTree>		fFileTreeMap;
	protected LogHandle						fLog;
	
	public AbstractSVDBArgFileIndex(
			String					project_name,
			String					arg_file,
			List<String>			file_paths,
			List<String>			include_paths,
			Map<String, String>		define_map) {
		super(project_name);
		
		fArgFile = arg_file;
		fBaseDir = new File(fArgFile).getParent();
		
		fFilePaths = new ArrayList<String>();
		if (file_paths != null) {
			fFilePaths.addAll(file_paths);
		}
		
		fIncludePaths = new ArrayList<String>();
		if (include_paths != null) {
			fIncludePaths.addAll(include_paths);
		}
		
		fDefineMap = new HashMap<String, String>();
		if (define_map != null) {
			fDefineMap.putAll(define_map);
		}
		
		fFileTreeMap = new HashMap<String, SVDBFileTree>();
	}
			
	
	public AbstractSVDBArgFileIndex(
			String			project_name,
			String			arg_file) {
		super(project_name);
		
		fLog = LogFactory.getDefault().getLogHandle("SVDBArgFileIndex");
		fArgFile = arg_file;
		
		fBaseDir      = new File(fArgFile).getParent();
		fFilePaths    = new ArrayList<String>();
		fIncludePaths = new ArrayList<String>();
		fDefineMap    = new HashMap<String, String>();
		
		InputStream in = openStream(expandVars(fArgFile, false));
		
		if (in != null) {
			ITextScanner sc = new InputStreamTextScanner(in, fArgFile);
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
			System.out.println("[ERROR] failed to open file \"" + fArgFile + "\"");
		}
		
		fFileTreeMap = new HashMap<String, SVDBFileTree>();
	}
	
	protected abstract InputStream openStream(String path);
	
	protected abstract long getLastModifiedTime(String path);
	
	protected String resolvePath(String path) {
		// relative to the base location
		if (path.startsWith("..")) {
			return fBaseDir + "/" + path;
		} else if (path.startsWith(".")) {
			if (path.equals(".")) {
				return fBaseDir;
			} else { 
				return fBaseDir + "/" + path.substring(2);
			}
		} else {
			return path;
		}
	}

	@Override
	protected void buildIndex() {
		System.out.println("[TODO] buildIndex");
	}

	/**
	 * Need to have a FileTree for each file. Should build this up
	 * while 
	 */
	@Override
	protected void buildPreProcFileMap() {
		System.out.println("[NOTE] AbstractSVDBArgFileIndex: buildPreProcFileMap()");
		
		for (String path : fFilePaths) {
			SVDBFile file = processPreProcFile(resolvePath(path));
			
			if (file == null) {
				System.out.println("Failed to find \"" + path + "\" \"" +
						resolvePath(path) + "\"");
			} else {
				fFileList.put(file.getFilePath(), file);
				SVDBFileTree ft = buildFileTree(null, file);

				processPreProcFile(file, ft, true);
			}
		}
		
		fFileListValid = true;
	}
	
	private void processPreProcFile(
			SVDBFile				file,
			SVDBFileTree			ft,
			boolean					add_to_map) {
		
		if (add_to_map) {
			System.out.println("file=" + file);
			fFileTreeMap.put(file.getFilePath(), ft);
		}
		
		// Iterate through included files
		for (SVDBItem it : ft.getSVDBFile().getItems()) {
			if (it.getType() == SVDBItemType.Include) {
				// See if we can find the path
				SVDBSearchResult<SVDBFile> inc_file;
				boolean is_local;
				
				if ((inc_file = findIncludedFile(it.getName())) != null) {
					is_local = true;
				} else if ((inc_file = findIncludedFileGlobal(it.getName())) != null) {
					is_local = false;
				} else {
					// Didn't find it anywhere...
					System.out.println("[ERROR] failed to find \"" + it.getName() + "\"");
					continue;
				}
				SVDBFileTree inc_file_ft = buildFileTree(ft, inc_file.getItem());
				
				ft.getIncludedFiles().add(inc_file_ft);
				inc_file_ft.getIncludedByFiles().add(ft);
				
				processPreProcFile(inc_file.getItem(), inc_file_ft, is_local);
			}
		}
	}
	
	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		SVDBFile ret = null;
		
		for (SVDBFile path : fFileList.values()) {
			if (path.getFilePath().endsWith(leaf)) {
				ret = path;
				break;
			}
		}
		
		if (ret != null) {
			return new SVDBSearchResult<SVDBFile>(ret, this);
		}
		
		// Iterate through the include paths
		for (String inc_path : fIncludePaths) {
			String try_path = resolvePath(inc_path) + "/" + leaf;
			InputStream in = openStream(try_path);

			System.out.println("[NOTE] try path \"" + try_path + "\"");
			if (in != null) {
				try {
					in.close();
				} catch (IOException e) {}
				ret = processPreProcFile(try_path);
				
				if (!fFileList.containsKey(ret.getFilePath())) {
					fFileList.put(ret.getFilePath(), ret);
				}
				break;
			}
		}
		
		if (ret != null) {
			return new SVDBSearchResult<SVDBFile>(ret, this);
		} else {
			return null;
		}
	}

	protected SVDBFileTree buildFileTree(
			SVDBFileTree			parent_ft,
			SVDBFile				file) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
		
		SVDBFileTree ft = new SVDBFileTree((SVDBFile)file.duplicate());

		if (parent_ft != null) {
			ft.getIncludedByFiles().add(parent_ft);
			parent_ft.getIncludedFiles().add(ft);
		}

		ft_utils.resolveConditionals(ft);

		return ft;
	}
	
	protected SVDBFile processPreProcFile(String path) {
		SVPreProcScanner 	sc = new SVPreProcScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.setObserver(ob);
		
		fLog.debug("processPreProcFile: path=" + path);
		String exp_path = expandVars(path, true);
		
		InputStream in = openStream(exp_path);
		
		if (in == null) {
			System.out.println("failed to open \"" + path + "\"");
			return null;
		}

		sc.init(in, path);
		sc.scan();
		
		try {
			in.close();
		} catch (IOException e) { }

		SVDBFile file = ob.getFiles().get(0);

		file.setLastModified(getLastModifiedTime(path));
		
		return file;
	}


	@Override
	protected boolean isLoadUpToDate() {
		// TODO Auto-generated method stub
		return false;
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}
	
	public void removeChangeListener(ISVDBIndexChangeListener l) {}
	

	public String getBaseLocation() {
		return fArgFile;
	}

	public int getIndexType() {
		return ISVDBIndex.IT_BuildPath;
	}

	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}

	public void rebuildIndex() {
		// TODO Auto-generated method stub

	}


	public SVDBFile parse(InputStream in, String path) {
		// TODO Auto-generated method stub
		return null;
	}

}
