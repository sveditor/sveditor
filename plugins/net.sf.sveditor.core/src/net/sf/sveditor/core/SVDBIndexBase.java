package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
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
	

	protected File								fBaseLocation;
	protected Queue<File>						fFileQueue;
	protected List<SVDBFile>					fFileList;
	protected Map<String, SVDBFileTree>			fFileMap;
	protected Map<File, Long>					fLastModifiedMap;
	protected boolean							fDisposed;
	protected ISVDBFileProvider					fFileProvider;
	private  Job								fScanJob;
	
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
	

	public SVDBIndexBase(File base_location, ISVDBFileProvider provider) {
		fBaseLocation = base_location;
		
		fFileQueue = new LinkedList<File>();
		fFileList  = new ArrayList<SVDBFile>();
		fLastModifiedMap = new HashMap<File, Long>();
		
		fFileProvider = provider;
		
		fScanJob = new Job("SVDBWorkspaceIndex") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				return SVDBIndexBase.this.run(monitor);
			}
		};
		
		fScanJob.setPriority(Job.LONG);
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
	
	public List<SVDBFile> getFileList() {
		return fFileList;
	}
	
	public Map<String, SVDBFileTree> getFileMap() {
		return fFileMap;
	}
	
	public SVDBFileTree getFileTree(String path) {
		Iterator<SVDBFileTree> it = fFileMap.values().iterator();
		
		while (it.hasNext()) {
			SVDBFileTree ft = it.next();
			
			if (ft.getFilePath().endsWith(path)) {
				return ft;
			}
		}
		
		return null;
	}
	
	private IStatus run(IProgressMonitor monitor) {
		SVPreProcScanner sc = new SVPreProcScanner();
		SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
		
		// First, scan all the files
		long start = System.currentTimeMillis();
		int num = fFileQueue.size();
		int idx = 0;
		List<File> scan_list = new ArrayList<File>();
		
		synchronized (fFileQueue) {
			while (fFileQueue.size() > 0) {
				scan_list.add(fFileQueue.poll());
			}
		}

		sc.setObserver(s_observer);
		
		while (!monitor.isCanceled() && idx < scan_list.size()) {
			File file = null;
			
			/*
			synchronized (fFileQueue) {
				if (fFileQueue.size() == 0) {
					break;
				} else {
					file = fFileQueue.poll();
				}
			}
			*/
			
			file = scan_list.get(idx++);
			
			if (file != null) {
				try {
					InputStream in = new FileInputStream(file);
					sc.scan(in, file.getAbsolutePath());
				} catch (IOException e) {
					
				}
			}
		}
		long end = System.currentTimeMillis();
		System.out.println("Scan " + num + " in " + (end-start));
		
		// Organize the files
		fFileMap = SVDBFileTreeUtils.organizeFiles(s_observer.getFiles());
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(fFileMap);
		
		start = System.currentTimeMillis();
		idx = 0;
		while (!monitor.isCanceled() && idx < scan_list.size()) {
			File file = null;
			

			/*
			synchronized (fFileQueue) {
				if (fFileQueue.size() == 0) {
					break;
				} else {
					file = fFileQueue.poll();
				}
			}
			 */
			file = scan_list.get(idx++);
			
			if (file != null) {
				SVDBFile svdb_f = null;
				boolean  existing = false;
				
				// First, parse the file
				
				try {
					InputStream in = new FileInputStream(file);
					
					svdb_f = SVDBFileFactory.createFile(
							in, file.getAbsolutePath(), fFileProvider, dp);
					
					in.close();
					
					if (fLastModifiedMap.containsKey(file)) {
						fLastModifiedMap.remove(file);
					}
					fLastModifiedMap.put(file, file.lastModified());
					
					
					// Find the file in the list and
					synchronized(fFileList) {
						for (int i=0; i<fFileList.size(); i++) {
							if (fFileList.get(i).getFilePath().equals(file)) {
								existing = true;
								fFileList.set(i, svdb_f);
								break;
							}
						}
					}
					
					if (!existing && svdb_f != null) {
						synchronized (fFileList) {
							fFileList.add(svdb_f);
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
			} else {
				System.out.println("[ERROR] exit indexer thread loop");
			}
		}
		end = System.currentTimeMillis();
		System.out.println("Parse " + scan_list.size() + " in " +
				(end-start));
		
		fFileList.clear();
		
		return Status.OK_STATUS;
	}
	
	protected void push(File file) {
		synchronized(fFileQueue) {
			fFileQueue.add(file);
		}

		/*
		synchronized (fScanJob) {
			if (fScanJob.getState() != Job.RUNNING) {
				fScanJob.schedule();
			}
		}
		 */
	}
	
	protected void startScan() {
		if (fScanJob.getState() != Job.RUNNING) {
			fScanJob.schedule();
		}
	}
	
	

}
