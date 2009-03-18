package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

/* 
 * Manages the index for a workspace location
 * 
 */
public class SVDBIndexBase implements ISVDBIndex {
	
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
	}
	
	public SVDBIndexBase(
			File 				base_location,
			int					index_type) {
		fBaseLocation = base_location;
		fIndexType    = index_type;
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();
		
		fFileMap = new HashMap<File, SVDBFile>();
		fFileMapValid = false;
		fFileMapBuilding = false;
		
		fPreProcFileMap   = new HashMap<File, SVDBFile>(); 
		fFileTreeValid    = false;
		fFileTreeBuilding = false;
		
		Job j = new Job("indexing") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				return SVDBIndexBase.this.updateFileIndex(monitor);
			}
		};
		
		j.setPriority(Job.LONG);
		j.schedule(5000);
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
	}
	
	public ISVDBIndex getSuperIndex() {
		return fSuperIndex;
	}

	public synchronized Map<File, SVDBFile> getFileDB() {
		
		if (fIndexType == IT_BuildPath) {
			if (!fFileMapValid) {
				updateFileIndex(new NullProgressMonitor());
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
					SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
					ft_utils.setIndex(this);
					
					SVDBFileTree ft = null;
					synchronized (file_list) {
						ft = ft_utils.createFileContext(pp_file, file_list);
					}
					SVDBFile svdb_file = parseFile(file, ft);
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
			
			fPreProcFileMap.put(file, f);
		}
		
		return fPreProcFileMap.get(file);
	}

	public synchronized Map<File, SVDBFile> getPreProcFileMap() {
		
		if (!fFileTreeValid) {
			buildFileTree(new NullProgressMonitor());
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
			SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
			Map<File, SVDBFile> pp_file_map = getPreProcFileMap();
			
			
			ft_utils.setIndex(fSuperIndex);

			Iterator<File> it = pp_file_map.keySet().iterator();

			while (it.hasNext()) {
				File file = it.next();
				
				if (!fFileMap.containsKey(file)) {
					SVDBFileTree ft = ft_utils.createFileContext(
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
			
			if (file.getPath().endsWith(leaf)) {
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
			System.out.println("end fileAdded");
		}
		
		if (fFileTreeValid) {
			if (fPreProcFileMap.containsKey(file)) {
				// hmmm... bad information
				fPreProcFileMap.remove(file);
			}
			
			fPreProcFileMap.put(file, createPreProcFile(file));
		}
		
		if (fFileMapValid) {
			SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
			Map<File, SVDBFile> pp_file_map = getPreProcFileMap();
			
			if (fFileMap.containsKey(file)) {
				fFileMap.remove(file);
			}
			
			SVDBFileTree ft = ft_utils.createFileContext(
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
			SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
			ft_utils.setIndex(this);
			Map<File, SVDBFile> pp_file_map = getPreProcFileMap();
			
			SVDBFileTree ft = ft_utils.createFileContext(
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
