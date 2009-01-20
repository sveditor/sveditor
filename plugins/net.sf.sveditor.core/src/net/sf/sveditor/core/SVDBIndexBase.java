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
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

/* 
 * Manages the index for a workspace location
 * 
 */
public class SVDBIndexBase implements ISVDBIndex {
	
	protected int								fIndexType;

	protected File								fBaseLocation;
//	protected Queue<File>						fFileQueue;
	
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
	
	private void startBuildFileTreeJob() {
		synchronized (this) {
			if (fBuildFileTreeJob == null) {
				fBuildFileTreeJob = new Job("BuildFileTree") {
					protected IStatus run(IProgressMonitor mon) {
						IStatus ret = SVDBIndexBase.this.buildFileTree(mon);
						synchronized (SVDBIndexBase.this) {
							fBuildFileTreeJob = null;
						}
						return ret;
					}
				};
				fFileTreeBuilding = true;
				fBuildFileTreeJob.setPriority(Job.SHORT);
				fBuildFileTreeJob.schedule();
			} else {
				System.out.println("Not starting new BuildFileTreeJob");
			}
		}
	}

	private void startBuildFileIndexJob() {
		synchronized (this) {
			if (fBuildFileIndexJob == null) {
				fBuildFileIndexJob = new Job("BuildFileIndex") {
					protected IStatus run(IProgressMonitor mon) {
						IStatus ret = SVDBIndexBase.this.buildFileIndex(mon);
						synchronized (SVDBIndexBase.this) {
							fBuildFileIndexJob = null;
						}
						return ret;
					}
				};
				fFileMapBuilding = true;
				fBuildFileIndexJob.setPriority(Job.SHORT);
				fBuildFileIndexJob.schedule();
			}
		}
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

	public Map<File, SVDBFile> getFileDB() {
		System.out.println("--> getFileDB()");
		
		if (fIndexType == IT_BuildPath) {
			synchronized (this) {
				if (!fFileMapValid) {
					if (!fFileMapBuilding) {
						// Start file map building
						startBuildFileIndexJob();
					}
					
					// Now, wait for file map to build
					while (!fFileMapValid) {
						try {
							wait();
						} catch (InterruptedException e) {
							e.printStackTrace();
						}
					}
				}
			}
		}
		
		System.out.println("<-- getFileDB()");
		return fFileMap;
	}
	
	public Map<File, SVDBFileTree> getFileTree() {
		
		System.out.println("--> getFileMap()");
		
		synchronized (this) {
			if (!fFileTreeValid) {
				if (!fFileTreeBuilding) {
					startBuildFileTreeJob();
				}
				
				// Now, wait for completion
				while (!fFileTreeValid) {
					try {
						wait();
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
			}
		}
		
		System.out.println("<-- getFileMap()");

		return fFileTreeMap;
	}
	
	private IStatus buildFileTree(IProgressMonitor monitor) {
		fFileTreeMap.clear();
		List<File> files = new ArrayList<File>();
		SVPreProcScanner sc = new SVPreProcScanner();
		SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
		
		System.out.println("--> buildFileTree()");
		
		sc.setObserver(s_observer);

		// Discover files

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

		synchronized (this) {
			fFileTreeValid = true;
			fFileTreeBuilding = false;
			notifyAll();
		}
		
		System.out.println("<-- buildFileTree()");
		return Status.OK_STATUS;
	}
	
	private IStatus buildFileIndex(IProgressMonitor monitor) {
		Map<File, SVDBFileTree> file_tree = getFileTree();
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(this);

		System.out.println("--> buildFileIndex()");
		
		fFileMap.clear();
		Iterator<File> it = file_tree.keySet().iterator();
		
		while (it.hasNext()) {
			File file = it.next();

			InputStream in = null;
			try {
				in = new FileInputStream(file);
			
				// Where do defines come from?
				dp.setFileContext(file_tree.get(file));
			
				SVDBFile svdb_f = SVDBFileFactory.createFile(
						in, file.getAbsolutePath(), fFileProvider, dp);
				fFileMap.put(file, svdb_f);
			
				in.close();
			} catch (IOException e) {
			} finally {
				if (in != null) {
					try {
						in.close();
					} catch (IOException e) { }
				}
			}
		}
		
		synchronized (this) {
			fFileMapValid = true;
			fFileMapBuilding = false;
			notifyAll();
		}
		
		System.out.println("<-- buildFileIndex()");
		
		return Status.OK_STATUS;
	}
	
	@Override
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

	@Override
	public int getIndexType() {
		return fIndexType;
	}

	@Override
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
