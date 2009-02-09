package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBPackageDecl;
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
	
	protected Map<File, SVDBFileTree>			fFileTreeMap;
	protected boolean							fFileTreeValid;
	protected boolean							fFileTreeBuilding;
	
	protected boolean							fDisposed;
	protected ISVDBFileProvider					fFileProvider;
	private  Job                                fBuildFileTreeJob;
	private  Job                                fBuildFileIndexJob;
	
	protected static final List<String>			fSVExtensions;
	protected static final List<String>			fIgnoreDirs;
	
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
			int					index_type,
			ISVDBFileProvider 	provider) {
		fBaseLocation = base_location;
		System.out.println("baseLocation=" + fBaseLocation);
		fIndexType    = index_type;
		
		fFileMap = new HashMap<File, SVDBFile>();
		fFileMapValid = false;
		fFileMapBuilding = false;
		
		fFileTreeMap = new HashMap<File, SVDBFileTree>();
		fFileTreeValid = false;
		fFileTreeBuilding = false;

		fFileProvider = provider;
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

	public synchronized Map<File, SVDBFile> getFileDB() {
		System.out.println("--> getFileDB()");
		
		if (fIndexType == IT_BuildPath) {
			if (!fFileMapValid) {
				updateFileIndex(new NullProgressMonitor());
			}
		}
		
		System.out.println("<-- getFileDB()");
		return fFileMap;
	}
	
	public synchronized SVDBFile findFile(File file) {
		Map<File, SVDBFileTree> file_tree = getFileTree();
		
		synchronized(file_tree) {
			if (file_tree.containsKey(file)) {
				synchronized (fFileMap) {
					if (!fFileMap.containsKey(file)) {
						// Create the file
						SVDBFile svdb_file = parseFile(file, file_tree.get(file));
						fFileMap.put(file, svdb_file);
					}
					
					return fFileMap.get(file);
				}
			}
		}
		
		return null;
	}
	
	public synchronized Map<File, SVDBFileTree> getFileTree() {
		
		System.out.println("--> getFileMap()");
		
		if (!fFileTreeValid) {
			buildFileTree(new NullProgressMonitor());
		}

		return fFileTreeMap;
	}
	
	private IStatus buildFileTree(IProgressMonitor monitor) {
		try {
			fFileTreeMap.clear();
			List<File> files = new ArrayList<File>();
			SVPreProcScanner sc = new SVPreProcScanner();
			SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
		
			System.out.println("--> buildFileTree()");
		
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
			
				try {
					InputStream in = new FileInputStream(f);
					sc.init(in, f.getAbsolutePath());
					sc.scan();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}

		
			fFileTreeMap.putAll(
					SVDBFileTreeUtils.organizeFiles(s_observer.getFiles()));
			
			Iterator<SVDBFileTree> it = fFileTreeMap.values().iterator();
			
			/*
			while (it.hasNext()) {
				SVDBFileTree f = it.next();
				System.out.println("[FILE] " + f.getFilePath());
				System.out.println("    Included-by files");
				for (SVDBFileTree fp : f.getIncludedByFiles()) {
					System.out.println("        " + fp.getFilePath());
				}
				System.out.println("    Included files");
				for (SVDBFileTree fp : f.getIncludedFiles()) {
					System.out.println("        " + fp.getFilePath());
				}
			}
			 */
		
		} catch (Exception e) { 
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileTreeValid = true;
				fFileTreeBuilding = false;
				notifyAll();
			}
			System.out.println("<-- buildFileTree()");
		}
		
		return Status.OK_STATUS;
	}
	
	private IStatus updateFileIndex(IProgressMonitor monitor) {
		try {
			Map<File, SVDBFileTree> file_tree = getFileTree();

			System.out.println("--> buildFileIndex()");

//			fFileMap.clear();
			Iterator<File> it = file_tree.keySet().iterator();

			while (it.hasNext()) {
				File file = it.next();
				
				if (!fFileMap.containsKey(file)) {
					SVDBFile svdb_file = parseFile(file, file_tree.get(file));
					
					synchronized(fFileMap) {
						fFileMap.put(file, svdb_file);
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			synchronized (this) {
				System.out.println("-> fileMapValid=true");
				fFileMapValid = true;
				fFileMapBuilding = false;
				notifyAll();
				System.out.println("<- fileMapValid=true");
			}

			System.out.println("<-- buildFileIndex()");
		}
		
		return Status.OK_STATUS;
	}
	
	private SVDBFile parseFile(File file, SVDBFileTree file_tree) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(this);
		SVDBFile svdb_file = null;
		InputStream in = null;
		try {
			in = new FileInputStream(file);

			// Where do defines come from?
			dp.setFileContext(file_tree);

			svdb_file = SVDBFileFactory.createFile(
					in, file.getAbsolutePath(), fFileProvider, dp);
			

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
	
	public SVDBFileTree findIncludedFile(String leaf) {
		Iterator<File> it = getFileTree().keySet().iterator();
		
		while (it.hasNext()) {
			File file = it.next();
			
			if (file.getPath().endsWith(leaf)) {
				return getFileTree().get(file);
			}
		}
		
		System.out.println("[WARN] failed to find include \"" + leaf + "\"");
		
		return null;
	}

	public int getIndexType() {
		return fIndexType;
	}

	public void rebuildIndex() {
		// TODO: force index and map to be invalid
		System.out.println("[TODO] SVDBIndexBase.rebuildIndex");
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
