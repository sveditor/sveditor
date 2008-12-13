package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;

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
	protected Map<File, Long>					fLastModifiedMap;
	protected boolean							fDisposed;
	private  Job								fScanJob;
	
	protected static final List<String>			fSVExtensions;
	
	static {
		fSVExtensions = new ArrayList<String>();
		
		fSVExtensions.add(".sv");
		fSVExtensions.add(".svh");
		fSVExtensions.add(".v");
		fSVExtensions.add(".V");
		fSVExtensions.add(".vl");
		fSVExtensions.add(".vlog");
	}
	

	public SVDBIndexBase(File base_location) {
		fBaseLocation = base_location;
		
		fFileQueue = new LinkedList<File>();
		fFileList  = new ArrayList<SVDBFile>();
		fLastModifiedMap = new HashMap<File, Long>();
		
		fScanJob = new Job("SVDBWorkspaceIndex") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				return SVDBIndexBase.this.run(monitor);
			}
		};
		
		fScanJob.setPriority(Job.LONG);
//		schedule();
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
	
	private IStatus run(IProgressMonitor monitor) {
		
		while (!monitor.isCanceled()) {
			File file = null;
			
			
			synchronized (fFileQueue) {
				if (fFileQueue.size() == 0) {
					break;
				} else {
					file = fFileQueue.poll();
				}
			}
			
			
			/*
			// Wait for an entry in the queue
			while (true) {
				synchronized (fFileQueue) {
					try {
						fFileQueue.wait();
						
						if (fFileQueue.size() > 0) {
							file = fFileQueue.poll();
							break;
						}
					} catch (InterruptedException e) {
						// exception -- exit
						System.out.println("Index Queue interrupted");
						break;
					}
				}
			}
			 */
			
			if (file != null) {
				SVDBFile svdb_f = null;
				boolean  existing = false;
				
				// First, parse the file
				
				try {
					InputStream in = new FileInputStream(file);
					
					System.out.println("[TODO] Need to pass in FileProvider when building index");
					// TODO: need to pass in the FileProvider
					svdb_f = SVDBFileFactory.createFile(in, 
							file.getAbsolutePath());
				} catch (Exception e) {
					e.printStackTrace();
				}
				
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
				
			} else {
				System.out.println("[ERROR] exit indexer thread loop");
			}
		}
		
		return Status.OK_STATUS;
	}
	
	protected void push(File file) {
		synchronized(fFileQueue) {
			fFileQueue.add(file);
		}
		
		synchronized (fScanJob) {
			if (fScanJob.getState() != Job.RUNNING) {
				fScanJob.schedule();
			}
		}
	}
	

}
