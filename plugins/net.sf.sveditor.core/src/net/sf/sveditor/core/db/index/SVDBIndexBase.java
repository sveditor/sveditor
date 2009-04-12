package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import javax.swing.filechooser.FileNameExtensionFilter;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.apache.tools.ant.DirectoryScanner;
import org.apache.tools.ant.Project;
import org.apache.tools.ant.types.FileSet;
import org.apache.tools.ant.types.selectors.FileSelector;
import org.apache.tools.ant.types.selectors.FilenameSelector;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;

/* 
 * Manages the index for a workspace location
 * 
 */
public abstract class SVDBIndexBase implements ISVDBIndex {
	
	protected int								fIndexType;

	protected File								fBaseLocation;
	
	protected Map<File, SVDBFile>				fFileMap;
	protected boolean							fFileMapValid;
	protected boolean							fFileMapBuilding;
	
	protected Map<File, SVDBFile>				fPreProcFileMap;
	protected boolean							fFileTreeValid;
	protected boolean							fFileTreeBuilding;
	
	protected boolean							fDisposed;
	
	protected static final List<String>			fSVExtensions;
	protected static final List<String>			fIgnoreDirs;
	
	protected List<ISVDBIndexChangeListener>	fIndexChageListeners;
	protected ISVDBIndex						fSuperIndex;
	
	protected static Pattern					fWinPathPattern;
	protected ISVDBIndexRegistry				fSVDBRegistry;
	protected SVDBFileTreeUtils					fFileTreeUtils;
	
	static {
		fSVExtensions = new ArrayList<String>();
		
		fSVExtensions.add(".sv");
		fSVExtensions.add(".svh");
		fSVExtensions.add(".v");
		fSVExtensions.add(".V");
		fSVExtensions.add(".vl");
		fSVExtensions.add(".vlog");
		
		fIgnoreDirs = new ArrayList<String>();
		fIgnoreDirs.add(".svn");
		fIgnoreDirs.add("CVS");
		
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	public SVDBIndexBase(
			File 				base_location,
			int					index_type) {
		FileSet	fs;
		
		Project null_p = new Project();
		
		fs = new FileSet();
		fs.setProject(null_p);
		fs.setIncludes("**/*.sv, **/*.svh, **/*.v");
		fs.setExcludes("**/.svn/**");
		fs.setDir(base_location);
		
		/*
		FilenameSelector file_sel = new FilenameSelector();
		file_sel.setName("*.sv");
		fs.add(file_sel);
		
		file_sel = new FilenameSelector();
		file_sel.setName("*.svh");
		fs.add(file_sel);
		
		file_sel = new FilenameSelector();
		file_sel.setName("*.v");
		fs.add(file_sel);
		
		 */
//		file_sel = new FilenameSelector();
//		file_sel.setNegate(true);
//		file_sel.setName("**/.svn/**");
//		fs.add(file_sel);
	
		long start = System.currentTimeMillis();
		DirectoryScanner s = fs.getDirectoryScanner();
		long end = System.currentTimeMillis();
		
		System.out.println("find time: " + (end-start));
		System.out.println("DirectoryScanner: " + s.getIncludedFilesCount() + " included");
		
		for (int i=0; i<s.getIncludedFilesCount(); i++) {
			System.out.println("    " + s.getIncludedFiles()[i]);
		}
		
		
		fBaseLocation = base_location;
		fIndexType    = index_type;
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();
		
		fFileMap = new HashMap<File, SVDBFile>();
		fFileMapValid = false;
		fFileMapBuilding = false;
		
		fPreProcFileMap   = new HashMap<File, SVDBFile>(); 
		fFileTreeValid    = false;
		fFileTreeBuilding = false;
		
		fFileTreeUtils    = new SVDBFileTreeUtils();
		
		fFileTreeUtils.setIndex(fSuperIndex);
	}
	
	public void init(ISVDBIndexRegistry registry) {
		fSVDBRegistry = registry;
	}
	
	public void load(List<SVDBFile> pp_files, List<SVDBFile> db_files) {
		
		synchronized (fPreProcFileMap) {
			fPreProcFileMap.clear();
		
			for (SVDBFile f : pp_files) {
				fPreProcFileMap.put(f.getFilePath(), f);
			}
			
			fFileTreeValid = true;
		}
		
		synchronized (fFileMap) {
			fFileMap.clear();
			
			for (SVDBFile f : db_files) {
				fFileMap.put(f.getFilePath(), f);
			}
			
			fFileMapValid = true;
		}
	}
	
	public boolean isLoaded() {
		return (fFileMapValid && fFileTreeValid);
	}

	public void dispose() {
		fDisposed = true;
	}
	
	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		
		if (!fDisposed) {
			dispose();
		}
	}
	
	public File getBaseLocation() {
		return fBaseLocation;
	}
	
	public void setSuperIndex(ISVDBIndex index) {
		fSuperIndex = index;
		fFileTreeUtils.setIndex(fSuperIndex);
	}
	
	public ISVDBIndex getSuperIndex() {
		return fSuperIndex;
	}

	public synchronized Map<File, SVDBFile> getFileDB() {
		
		if (fIndexType == IT_BuildPath) {
			if (!fFileMapValid) {
				if (!fSVDBRegistry.loadPersistedData(this)) {
					updateFileIndex(new NullProgressMonitor());
				}
			}
		}
		
		return fFileMap;
	}
	
	public synchronized SVDBFile findFile(File file) {
		SVDBFile pp_file = findPreProcFile(file);
		Map<File, SVDBFile> file_list = getPreProcFileMap();

		if (pp_file != null) {
			synchronized (fFileMap) {
				if (!fFileMap.containsKey(file)) {
					// Create the file
					// TODO: opportunity for caching
					
					SVDBFileTree ft = null;
					synchronized (file_list) {
						System.out.println("createFileContext: " + pp_file.getFilePath());
						long start = System.currentTimeMillis();
						ft = fFileTreeUtils.createFileContext(pp_file, file_list);
						long end = System.currentTimeMillis();
						
						System.out.println("creating context took: " + (end-start));
					}
					
					long start = System.currentTimeMillis();
					SVDBFile svdb_file = parseFile(file, ft);
					long end = System.currentTimeMillis();
					
					System.out.println("parse took: " + (end-start));
					fFileMap.put(file, svdb_file);
				}

				return fFileMap.get(file);
			}
		}
		
		return null;
	}

	public synchronized SVDBFile findPreProcFile(File file) {
		
		if (!fPreProcFileMap.containsKey(file)) {
			SVDBFile f = createPreProcFile(file);
			
			if (f == null) {
				System.out.println("createPreProcFile returned null");
			}
			
			fPreProcFileMap.put(file, f);
			
			fileAdded(file);
		}
		
		if (!fPreProcFileMap.containsKey(file)) {
			System.out.println("createPreProcFile: still doesn't contain \"" + file.getPath() + "\"");
		} else if (fPreProcFileMap.get(file) == null) {
			System.out.println("createPreProcFile: contains key, but null");
		}
		
		return fPreProcFileMap.get(file);
	}

	public synchronized Map<File, SVDBFile> getPreProcFileMap() {
		
		if (!fFileTreeValid) {
			if (!fSVDBRegistry.loadPersistedData(this)) {
				buildFileTree(new NullProgressMonitor());
			}
		}

		return fPreProcFileMap;
	}
	
	private synchronized IStatus buildFileTree(IProgressMonitor monitor) {
		try {
			List<File>       files         = new ArrayList<File>();
			SVPreProcScanner sc            = new SVPreProcScanner();
			SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
		
			sc.setObserver(s_observer);

			// 	Discover files

			if (monitor != null) {
				monitor.setTaskName("Discovering Files");
			}
		
			find_files(fBaseLocation, files, monitor);
				
			if (monitor != null) {
				monitor.setTaskName("Scanning files");
			}

			for (File f : files) {
				if (fPreProcFileMap.containsKey(f)) {
					fPreProcFileMap.remove(f);
				}
				fPreProcFileMap.put(f, createPreProcFile(f));
			}
		} catch (Exception e) { 
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileTreeValid = true;
				fFileTreeBuilding = false;
				notifyAll();
			}
		}
		
		return Status.OK_STATUS;
	}
	
	private SVDBFile createPreProcFile(File file) {
		SVPreProcScanner sc            = new SVPreProcScanner();
		SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
	
		sc.setObserver(s_observer);

		try {
			InputStream in = new FileInputStream(file);
			sc.init(in, file.getAbsolutePath());
			sc.scan();
		} catch (IOException e) {
			e.printStackTrace();
		}

		if (s_observer.getFiles().size() > 0) {
			return s_observer.getFiles().get(0);
		} else {
			return null;
		}
	}
	
	private synchronized IStatus updateFileIndex(IProgressMonitor monitor) {
		try {
			Map<File, SVDBFile> pp_file_map = getPreProcFileMap();
			
			

			Iterator<File> it = pp_file_map.keySet().iterator();

			while (it.hasNext()) {
				File file = it.next();
				
				if (!fFileMap.containsKey(file)) {
					SVDBFileTree ft = fFileTreeUtils.createFileContext(
							pp_file_map.get(file), pp_file_map);
					SVDBFile svdb_file = parseFile(file, ft);
					
					synchronized(fFileMap) {
						fFileMap.put(file, svdb_file);
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileMapValid = true;
				fFileMapBuilding = false;
				notifyAll();
			}

		}
		
		return Status.OK_STATUS;
	}
	
	private SVDBFile parseFile(File file, SVDBFileTree file_tree) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();
		SVDBFile svdb_file = null;
		InputStream in = null;
		try {
			in = new FileInputStream(file);

			// Where do defines come from?
			dp.setFileContext(file_tree);

			svdb_file = SVDBFileFactory.createFile(
					in, file.getAbsolutePath(), dp);
			

			in.close();
		} catch (IOException e) {
		} finally {
			if (in != null) {
				try {
					in.close();
				} catch (IOException e) { }
			}
		}
		
		return svdb_file;
	}
	
	public SVDBFile findIncludedFile(String leaf) {
		Iterator<File> it = getPreProcFileMap().keySet().iterator();
		
		while (it.hasNext()) {
			File file = it.next();
			
			// Normalize the path so this works on Windows
			String path_norm =
				fWinPathPattern.matcher(file.getPath()).replaceAll("/");
			
			if (path_norm.endsWith(leaf)) {
				// TODO: opportunity for caching
				return getPreProcFileMap().get(file);
			}
		}
		
		return null;
	}

	public int getIndexType() {
		return fIndexType;
	}

	public void rebuildIndex() {
		// TODO: force index and map to be invalid
		System.out.println("[TODO] SVDBIndexBase.rebuildIndex");
	}
	
	public void addChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.add(l);
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.remove(l);
	}

	protected void fileRemoved(File file) {
		fPreProcFileMap.remove(file);
		SVDBFile svdb_file = fFileMap.remove(file);

		if (svdb_file != null) {
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_REMOVED, svdb_file);
			}
		}
	}
	
	protected void fileAdded(File file) {
		// First, decide whether this is a file to ignore
		if (file.getName().lastIndexOf('.') != -1) {
			String ext = file.getName().substring(
					file.getName().lastIndexOf('.'));
			
			if (!fSVExtensions.contains(ext)) {
				return;
			}
			
			// Next, check whether there is an ignore dir on the path
			File parent = file.getParentFile();
			File last_parent = null;
			
			while (parent != null &&
					(last_parent == null || !last_parent.equals(parent))) {
				if (fIgnoreDirs.contains(parent.getName())) {
					return;
				}
				last_parent = parent;
				parent = file.getParentFile();
			}
		} else {
			return;
		}
		
		if (fFileTreeValid) {
			if (fPreProcFileMap.containsKey(file)) {
				// hmmm... bad information
				fPreProcFileMap.remove(file);
			}
			
			fPreProcFileMap.put(file, createPreProcFile(file));
		}
		
		if (fFileMapValid) {
			Map<File, SVDBFile> pp_file_map = getPreProcFileMap();
			
			if (fFileMap.containsKey(file)) {
				fFileMap.remove(file);
			}
			
			SVDBFileTree ft = fFileTreeUtils.createFileContext(
					pp_file_map.get(file), pp_file_map);
			SVDBFile svdb_file = parseFile(file, ft);
			
			synchronized(fFileMap) {
				fFileMap.put(file, svdb_file);
			}
			
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_ADDED, svdb_file);
			}
		}
	}
	
	protected void fileChanged(File file) {
		
		if (fPreProcFileMap.containsKey(file)) {
			fPreProcFileMap.remove(file);
			fPreProcFileMap.put(file, createPreProcFile(file));
		}

		if (fFileMap.containsKey(file)) {
			Map<File, SVDBFile> pp_file_map = getPreProcFileMap();
			
			SVDBFileTree ft = fFileTreeUtils.createFileContext(
					pp_file_map.get(file), pp_file_map);
			SVDBFile svdb_file = parseFile(file, ft);
			SVDBFile svdb_file_e = fFileMap.get(file);

			// Merge any new content with the existing
			SVDBFileMerger.merge(svdb_file_e, svdb_file, null, null, null);
			
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_CHANGED, svdb_file_e);
			}
		}
	}

	private static void find_files(
			File 				parent, 
			List<File> 			files,
			IProgressMonitor	monitor) {
		for (File f : parent.listFiles()) {
			if (monitor != null && monitor.isCanceled()) {
				return;
			}
			if (f.isDirectory()) {
				if (!fIgnoreDirs.contains(f.getName())) {
					find_files(f, files, monitor);
				}
			} else {
				String name = f.getName();
				int last_dot;
				
				if ((last_dot = name.lastIndexOf('.')) >= 0) {
					String suffix = name.substring(last_dot);
					if (fSVExtensions.contains(suffix)) {
						files.add(f);
					}
				}
			}
		}
	}
}
