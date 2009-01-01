package net.sf.sveditor.core;

import java.io.File;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBFilesystemIndex extends SVDBIndexBase {
	
	private Job						fRefreshJob;
	private int						fIndex;
	
	public SVDBFilesystemIndex(File root, ISVDBFileProvider provider) {
		super(root, provider);
		
		// Recurse through the files
		fRefreshJob = new Job("refreshJob") {

			@Override
			protected IStatus run(IProgressMonitor monitor) {
				return SVDBFilesystemIndex.this.run_refresh(monitor);
			}
		};
		
		// recurse down 'root', finding SystemVerilog files
		recurse(root);
		
		fRefreshJob.setPriority(Job.LONG);
		fRefreshJob.schedule();
	}
	
	private void recurse(File root) {
		for (File f : root.listFiles()) {
			if (f.isFile()) {
				String ext;
				
				if (f.getName().lastIndexOf('.') != -1) {
					ext = f.getName().substring(f.getName().lastIndexOf('.'));
					
					if (fSVExtensions.contains(ext)) {
						push(f);
					}
				}
			} else if (f.isDirectory() && !fIgnoreDirs.contains(f.getName())) {
				recurse(f);
			}
		}
	}
	
	public void dispose() {
		super.dispose();
		
		fRefreshJob.cancel();
	}
	
	
	protected IStatus run_refresh(IProgressMonitor monitor) {
		
		synchronized (fFileList) {
			for (int i=0; i<1000; i++) {
				if (i+fIndex > fFileList.size()) {
					fIndex = 0;
					break;
				}
				
				if (i+fIndex < fFileList.size()) {
					File file = fFileList.get(i+fIndex).getFilePath();

					if (!file.exists()) {
						fFileList.remove(i+fIndex);
						fLastModifiedMap.remove(file);
						continue;
					}

					long lastModified = fLastModifiedMap.get(file);
					if (file.lastModified() > lastModified) {
						// push this file onto the queue for update
						push(file);
					}
				}
			}
		}
		
		fRefreshJob.schedule(5000);
		return Status.OK_STATUS;
	}
	
	
}
