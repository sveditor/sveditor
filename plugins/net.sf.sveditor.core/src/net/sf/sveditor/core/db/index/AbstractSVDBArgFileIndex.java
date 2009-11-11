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
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

public abstract class AbstractSVDBArgFileIndex extends AbstractSVDBIndex {
	
	protected String				fArgFile;
	protected String				fBaseDir;
	protected List<String>			fFilePaths;
	protected List<String>			fIncludePaths;
	protected Map<String, String>	fDefineMap;
	protected LogHandle				fLog;
	
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
				fFilePaths.add(f);
			}
			
			for (String inc : scanner.getIncludePaths()) {
				fIncludePaths.add(inc);
			}
			
		} else {
			System.out.println("[ERROR] failed to open file \"" + fArgFile + "\"");
		}
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
		// TODO Auto-generated method stub

	}

	@Override
	protected void buildPreProcFileMap() {
		
		for (String path : fFilePaths) {
			SVDBFileTree ft = buildFileTree(null, path);
		}
		
	}
	
	
	
	@Override
	public SVDBFile findIncludedFile(String leaf) {
		// TODO Auto-generated method stub
		return super.findIncludedFile(leaf);
	}

	protected SVDBFileTree getFileTree() {
		return null;
	}

	protected SVDBFileTree buildFileTree(
			SVDBFileTree			parent_ft,
			String					path) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
		String resolved_path = resolvePath(path);
		SVDBFile file = processPreProcFile(resolved_path);
		
		if (file != null) {
			fFileList.put(path, file);
			SVDBFileTree ft = new SVDBFileTree((SVDBFile)file.duplicate());
			
			if (parent_ft != null) {
				ft.getIncludedByFiles().add(parent_ft);
				parent_ft.getIncludedFiles().add(ft);
			}
			
			ft_utils.resolveConditionals(ft);
			
			for (SVDBItem it : ft.getSVDBFile().getItems()) {
				if (it.getType() == SVDBItemType.Include) {
					// See if we can find the path
					SVDBFile inc_file = findIncludedFileGlobal(it.getName());
				}
			}
		
			return ft;
		}
		
		return null;
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
