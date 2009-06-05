package net.sf.sveditor.core.db.index;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

public abstract class AbstractSVDBLibIndex extends AbstractSVDBIndex {
	protected Map<String, SVDBFileTree>		fFileTreeMap;
	protected String						fRoot;
	protected List<AbstractSVFileMatcher>	fFileMatchers;
	
	
	public AbstractSVDBLibIndex(String project, String root) {
		super(project);
		
		fFileTreeMap 	= new HashMap<String, SVDBFileTree>();
		fRoot 			= root;
		fFileMatchers	= new ArrayList<AbstractSVFileMatcher>();
	}


	public void addChangeListener(ISVDBIndexChangeListener l) {}
	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	
	@Override
	public String getBaseLocation() {
		return fRoot;
	}
	
	public String getResolvedBaseLocation() {
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();
		
		String exp = fRoot;
		try {
			exp = mgr.performStringSubstitution(fRoot);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		return exp;
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
			SVDBFile pp_file = findPreProcFile(fRoot);
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			prepareFileTree(ft_root, null);
		}
	}
	
	@Override
	protected boolean isLoadUpToDate() {
		List<String> fileList = getFileList();
		
		if (fileList.size() != fFileList.size()) {
			debug("    fileList.size=" + fileList.size() + " fFileList.size=" + fFileList.size());
			return false;
		}
		
		// Now, iterate through and check lastModified timestamps
		for (String f : fileList) {
			SVDBFile svdb_f = fFileList.get(f);
			
			if (svdb_f == null || 
					(svdb_f.getLastModified() != getLastModifiedTime(f))) {
				if (svdb_f == null) {
					debug("    Failed to find file \"" + f + "\"");
				} else {
					debug("    file \"" + f + "\": saved timestamp: " +
							svdb_f.getLastModified() + " ; current timestamp: " + getLastModifiedTime(f));
				}
				return false;
			}
		}
		
		return true;
	}
	

	public SVDBFile parse(InputStream in, String path) {
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		SVDBFileFactory scanner = new SVDBFileFactory(dp);
		
		getFileDB();
		
		SVDBFileTree file_tree = fFileTreeMap.get(path);
		
		if (file_tree != null) {
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

	protected void buildPreProcFileMap() {
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
	
	protected abstract InputStream openStream(String path);

	protected abstract long getLastModifiedTime(String file);

	protected void buildIndex() {
		System.out.println("--> buildIndex()");
		long start = System.currentTimeMillis();
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		
		SVDBFile pp_file = findPreProcFile(getResolvedBaseLocation());

		if (pp_file == null) {
			System.out.println("Failed to find file \"" + getResolvedBaseLocation() + "\"");
			System.out.println("    class: " + getClass().getName());
		}
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		prepareFileTree(ft_root, null);
		processFile(ft_root, dp);
		
		fFileIndexValid = true;
		long end = System.currentTimeMillis();
		System.out.println("<-- buildIndex(" + (end-start) + ")");
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
	
	protected SVDBFile findIncludeFile(String path) {
		for (String p : getPreProcFileMap().keySet()) {
			if (p.endsWith(path)) {
				return getPreProcFileMap().get(p);
			}
		}
		
		return null;
	}

	protected void addIncludeFiles(
			SVDBFileTree 		root, 
			SVDBScopeItem 		scope) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Include) {
				debug("Include file: " + it.getName());
				SVDBFile f = findIncludeFile(it.getName());

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
	
	private void debug(String msg) {
		
	}

}
