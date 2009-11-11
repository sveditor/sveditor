package net.sf.sveditor.core.db.index;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

/*
 * SVDBFileSystemCompileIndex
 * 
 * This index uses a complete set of imformation about the SV sources to index. 
 * In this regard, it is most similar to a verilog compiler.
 * 
 */
public abstract class AbstractSVDBCompileIndex extends AbstractSVDBIndex {
	
	private List<String>							fIncludePaths;
	private List<String>							fFilePaths;
	private LogHandle								fLog;
	private Map<String, SVDBFileTree>				fFileTreeMap;
	private Map<String, String>						fDefineMap;
	
	public AbstractSVDBCompileIndex(String project_name) {
		super(project_name);
		
		fIncludePaths 	= new ArrayList<String>();
		fFilePaths 		= new ArrayList<String>();
		fFileTreeMap	= new HashMap<String, SVDBFileTree>();
		fLog			= LogFactory.getDefault().getLogHandle(
				"SVDBFileSystemCompileIndex");
		fDefineMap 		= new HashMap<String, String>();
	}
	
	public void addIncludePath(String path) {
		fIncludePaths.add(path);
	}
	
	public void addFilePath(String path) {
		fFilePaths.add(path);
	}
	
	public void addDefine(String key, String val) {
		if (fDefineMap.containsKey(key)) {
			fDefineMap.remove(key);
		}
		
		fDefineMap.put(key, val);
	}
	
	public void addDefine(String key) {
		if (fDefineMap.containsKey(key)) {
			fDefineMap.remove(key);
		}
		
		fDefineMap.put(key, "1");
	}

	@Override
	protected void buildIndex() {
		
		for (String file : fFilePaths) {
			try {
				buildIndex(file);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		fFileIndexValid = true;
		fFileListValid = true;
	}
	
	protected void buildIndex(String path) {
		fLog.debug("--> buildIndex()");
		long start = System.currentTimeMillis();
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		
		dp.addDefines(fDefineMap);
		
		// SVDBFile pp_file = findPreProcFile(getResolvedBaseLocation());
		SVDBFile pp_file = processPreProcFile(path);

		if (pp_file == null) {
			System.out.println("Failed to find file \"" + path + "\"");
			System.out.println("    class: " + getClass().getName());
			fFileIndexValid = true;
			return;
		}
		
		if (fFileList.containsKey(path)) {
			fFileList.remove(path);
		}
		fFileList.put(path, pp_file);
		
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		prepareFileTree(ft_root, null);
		processFile(ft_root, dp);
		
		long end = System.currentTimeMillis();
		fLog.debug("<-- buildIndex(" + (end-start) + ")");
	}
	
	protected SVDBFile processPreProcFile(String path) {
		SVPreProcScanner 	sc = new SVPreProcScanner();
		SVDBPreProcObserver ob = new SVDBPreProcObserver();

		sc.setObserver(ob);
		
		fLog.debug("processPreProcFile: path=" + path);
		InputStream in = openStream(path);
		
		if (in == null) {
			System.out.println("failed to open \"" + path + "\"");
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
	
	protected void processFile(
			SVDBFileTree				path,
			SVPreProcDefineProvider		dp) {
		dp.setFileContext(path);
		
		SVDBFileFactory scanner = new SVDBFileFactory(dp);
		
		String path_s = path.getFilePath();

		InputStream in = openStream(path_s);
		BufferedInputStream in_b = new BufferedInputStream(in);

		SVDBFile svdb_f = scanner.parse(in_b, path.getFilePath());
		
		svdb_f.setLastModified(getLastModifiedTime(path.getFilePath()));

		fFileIndex.put(path.getFilePath(), svdb_f);

		// Now, recurse through the files included
		for (SVDBFileTree ft_t : path.getIncludedFiles()) {
			if (!fFileIndex.containsKey(ft_t.getFilePath())) {
				processFile(ft_t, dp);
			}
		}

		try {
			in.close();
		} catch (IOException e) { }
	}	
	
	protected void prepareFileTree(
			SVDBFileTree 				root,
			SVDBFileTree				parent) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
		
		ft_utils.resolveConditionals(root);
		
		String path = root.getFilePath();
		if (fFileTreeMap.containsKey(path)) {
			fFileTreeMap.remove(path);
		}
		fFileTreeMap.put(path, root);
		
		if (parent != null) {
			root.getIncludedByFiles().add(parent);
		}
		
		addIncludeFiles(root, root.getSVDBFile());
	}
	
	protected void addIncludeFiles(
			SVDBFileTree 		root, 
			SVDBScopeItem 		scope) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Include) {
				fLog.debug("Include file: " + it.getName());
				
				SVDBFile f = findIncludedFileGlobal(it.getName());

				if (f != null) {
					SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.duplicate());
					root.getIncludedFiles().add(ft);
					prepareFileTree(ft, root);
				} else {
					System.out.println("failed to find file " + it.getName());
				}
				
			} else if (it instanceof SVDBScopeItem) {
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}	

	public SVDBFile findIncludedFile(String leaf) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		
		Iterator<String> it = map.keySet().iterator();
		
		while (it.hasNext()) {
			String f = it.next();
			
			String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
			
			if (norm_path.endsWith(leaf)) {
				return map.get(f);
			}
		}
		
		// Otherwise, look down the include paths for this index
		for (String inc_path : fIncludePaths) {
			String try_path = inc_path + "/" + leaf;
			InputStream in = openStream(try_path);
			
			if (in != null) {
				SVDBFile file = processPreProcFile(try_path);
				map.put(try_path, file);
				
				try {
					in.close();
				} catch (IOException e) {}
				
				return file;
			}
		}
		
		return null;
	}
	
	protected abstract InputStream openStream(String path);

	protected abstract long getLastModifiedTime(String path);
	
	public String getResolvedLocation(String base_location) {
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();

		String exp = base_location;
		try {
			exp = mgr.performStringSubstitution(exp);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		return exp;
	}

	@Override
	protected void buildPreProcFileMap() {}

	@Override
	protected boolean isLoadUpToDate() {
		System.out.println("[TODO] AbstractSVDBCompileIndex.isLoadUpToDate()");
		 
		return false;
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}

	public String getBaseLocation() {
		return "";
	}

	public int getIndexType() {
		return 0;
	}

	public String getTypeID() {
		return "net.sf.sveditor.compileIndex";
	}

	public void rebuildIndex() {}

	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	public SVDBFile parse(InputStream in, String path) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();
		SVDBFileFactory scanner = new SVDBFileFactory(dp);
		
		dp.addDefines(fDefineMap);
		
		getFileDB();
		
		SVDBFileTree file_tree = fFileTreeMap.get(path);
		
		if (file_tree == null) {
			// Create an entry if possible
			SVDBFile svdb_f = findPreProcFile(path);
			
			if (svdb_f != null) {
				file_tree = new SVDBFileTree((SVDBFile)svdb_f.duplicate());
				
				prepareFileTree(file_tree, null);
			}
		}
		
		if (file_tree != null) {
			dp.setFileContext(file_tree);
			SVDBFile svdb_f = scanner.parse(in, file_tree.getFilePath());
			svdb_f.setLastModified(getLastModifiedTime(path));
			return svdb_f;
		} else {
			fLog.debug("path \"" + path + "\" not in FileTree map");
			for (SVDBFileTree ft : fFileTreeMap.values()) {
				fLog.debug("    " + ft.getFilePath());
			}
			return null;
		}
	}
}
