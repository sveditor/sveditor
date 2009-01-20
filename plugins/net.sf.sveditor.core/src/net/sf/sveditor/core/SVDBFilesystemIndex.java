package net.sf.sveditor.core;

import java.io.File;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class SVDBFilesystemIndex extends SVDBIndexBase {
	
	public SVDBFilesystemIndex(
			File 					root, 
			int						index_type,
			ISVDBFileProvider 		provider) {
		super(root, index_type, provider);
	}
	
	
	public void dispose() {
		super.dispose();
	}
	
}
