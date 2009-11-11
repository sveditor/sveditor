package net.sf.sveditor.core.db.index;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

public abstract class AbstractSVDBLibIndex extends AbstractSVDBIndex {
	protected Map<String, SVDBFileTree>		fFileTreeMap;
	protected String						fRoot;
	protected String						fResolvedRoot;
	protected List<AbstractSVFileMatcher>	fFileMatchers;
	protected LogHandle						fLog;
	
	
	public AbstractSVDBLibIndex(String project, String root) {
		super(project);
		
		fFileTreeMap 	= new HashMap<String, SVDBFileTree>();
		fRoot 			= root;
		fFileMatchers	= new ArrayList<AbstractSVFileMatcher>();
		fLog = LogFactory.getDefault().getLogHandle("AbstractSVDBLibIndex");
	}


	public void addChangeListener(ISVDBIndexChangeListener l) {}
	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	
	public String getBaseLocation() {
		return fRoot;
	}
	
	public String getResolvedBaseLocation() {
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();

		if (fResolvedRoot == null) {
			String exp = fRoot;
			fResolvedRoot = fRoot;
			if (exp.startsWith("${workspace_loc}")) {
				fResolvedRoot = fResolvedRoot.substring("${workspace_loc}".length());
			}
			try {
				fResolvedRoot = mgr.performStringSubstitution(fRoot);
			} catch (CoreException e) {
				e.printStackTrace();
			}
			if (exp.startsWith("${workspace_loc}")) {
				fResolvedRoot = "${workspace_loc}" + fResolvedRoot;
			}
		}
		
		return fResolvedRoot;
	}
	
	public int getIndexType() {
		return ISVDBIndex.IT_BuildPath;
	}


	public void rebuildIndex() {
		// TODO Auto-generated method stub

	}
	
	@Override
	public void load(List<SVDBFile> ppFiles, List<SVDBFile> dbFiles) {
		super.load(ppFiles, dbFiles);
		
		if (fFileIndexValid && fFileListValid) {
			SVDBFile pp_file = findPreProcFile(getResolvedBaseLocation());
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			prepareFileTree(ft_root, null);
		}
	}

	/**
	 * findIncludedFile()
	 * 
	 * Search the include paths within this index
	 */
	public SVDBFile findIncludedFile(String path) {
		String root_dir = new File(getResolvedBaseLocation()).getParent();
		String inc_path = root_dir + "/" + path;
		
		Map<String, SVDBFile> pp_map = getPreProcFileMap();
		
		if (pp_map.containsKey(inc_path)) {
			return pp_map.get(inc_path);
		} else {
			SVDBFile pp_file = null;
			InputStream in = openStream(inc_path);
			
			if (path.contains("ovm.svh")) {
				System.out.println("OpenStream \"" + inc_path + "\": " + in);
			}
			
			if (in != null) {
				pp_file = processPreProcFile(inc_path);
			
				if (pp_file != null) {
					pp_map.put(inc_path, pp_file);
				}
				try {
					in.close();
				} catch (IOException e) { }
				
			}
			return pp_file;
		}
	}
	
	@Override
	protected boolean isLoadUpToDate() {
		
		// Now, iterate through and check lastModified timestamps
		for (SVDBFile svdb_f : fFileList.values()) {
			InputStream in = openStream(svdb_f.getFilePath());
			String path = svdb_f.getFilePath();
			
			if (in == null ||  
					(svdb_f.getLastModified() != getLastModifiedTime(path))) {
				debug("    file \"" + path + "\": saved timestamp: " +
						svdb_f.getLastModified() + " ; current timestamp: " + 
						getLastModifiedTime(path));
				return false;
			} else {
				try {
					in.close();
				} catch (IOException e) { }
			}
		}
		
		return true;
	}
	

	public SVDBFile parse(InputStream in, String path) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();
		SVDBFileFactory scanner = new SVDBFileFactory(dp);
		
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
			debug("path \"" + path + "\" not in FileTree map");
			for (SVDBFileTree ft : fFileTreeMap.values()) {
				debug("    " + ft.getFilePath());
			}
			return null;
		}
	}

	/**
	 * buildPreProcFileMap()
	 * 
	 * Creating the pre-processor map requires that we build the
	 * 
	 */
	protected void buildPreProcFileMap() {
		// Say the index is valid for now
		fFileListValid = true;
		
		// Getting the file database will ensure the
		// pre-proc map is up-to-date
		// getFileDB();
	}
	
	/*
	protected void buildPreProcFileMap_2() {
		Iterator<String> entries = getFileList().iterator();
		
		while (entries.hasNext()) {
			String path = entries.next();
			SVPreProcScanner 	sc = new SVPreProcScanner();
			SVDBPreProcObserver ob = new SVDBPreProcObserver();

			sc.setObserver(ob);
			
			InputStream in = openStream(path);

			sc.init(in, path);
			sc.scan();
			
			try {
				in.close();
			} catch (IOException e) { }

			SVDBFile file = ob.getFiles().get(0);

			if (fFileList.containsKey(path)) {
				fFileList.remove(path);
			}
			
			file.setLastModified(getLastModifiedTime(path));
			
			fFileList.put(path, file);
		}
		
		fFileListValid = true;
	}
	 */
	
	/*
	protected List<String> getFileList() {
		List<String> ret; 
		debug("AbstractSVDBLibIndex.getFileList()");
		
		if (fFileMatchers.size() == 1) {
			ret = fFileMatchers.get(0).findIncludedPaths();
		} else {
			ret = new ArrayList<String>();
			for (AbstractSVFileMatcher m : fFileMatchers) {
				ret.addAll(m.findIncludedPaths());
			}
		}
		
		debug("getFileList: " + getBaseLocation());
		for (String f : ret) {
			debug("    " + f);
		}
		
		return ret;
	}
	 */
	
	protected abstract InputStream openStream(String path);

	protected abstract long getLastModifiedTime(String file);

	/**
	 * buildIndex()
	 * 
	 * Called by AbstractSVDBIndex to build the index
	 */
	protected void buildIndex() {
		fLog.debug("--> buildIndex()");
		long start = System.currentTimeMillis();
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		
		// SVDBFile pp_file = findPreProcFile(getResolvedBaseLocation());
		SVDBFile pp_file = processPreProcFile(getResolvedBaseLocation());

		if (pp_file == null) {
			System.out.println("Failed to find file \"" + getResolvedBaseLocation() + "\"");
			System.out.println("    class: " + getClass().getName());
			fFileIndexValid = true;
			return;
		}
		
		if (fFileList.containsKey(getResolvedBaseLocation())) {
			fFileList.remove(getResolvedBaseLocation());
		}
		fFileList.put(getResolvedBaseLocation(), pp_file);
		
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		prepareFileTree(ft_root, null);
		processFile(ft_root, dp);
		
		fFileIndexValid = true;
		fFileListValid = true;
		
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
			System.out.println(getClass().getName() + ": failed to open \"" + path + "\"");
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
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
				debug("Include file: " + it.getName());
				
				SVDBFile f = findIncludedFileGlobal(it.getName());

				if (f != null) {
					SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.duplicate());
					root.getIncludedFiles().add(ft);
					prepareFileTree(ft, root);
				} else {
					System.out.println("AbstractSVDBLibIndex: " +
							getBaseLocation() + " failed to find include file " + it.getName());
				}
				
			} else if (it instanceof SVDBScopeItem) {
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}
	
	public SVDBFile findPreProcFile(String path) {
		debug("findPreProcFile \"" + path + "\"");
		if (fFileList.containsKey(path)) {
			return fFileList.get(path);
		} else {
			InputStream in = openStream(path);
			
			if (in != null) {
				SVDBFile file = processPreProcFile(path);
				fFileList.put(path, file);
				try {
					in.close();
				} catch (IOException e) { }
				
				return file;
			}
		}
		return null;
	}
	
	private void debug(String msg) {
		fLog.debug(msg);
	}

}
