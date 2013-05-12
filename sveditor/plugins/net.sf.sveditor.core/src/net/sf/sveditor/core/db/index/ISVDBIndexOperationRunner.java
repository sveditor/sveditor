package net.sf.sveditor.core.db.index;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexOperationRunner {
	
	void execOp(
			IProgressMonitor 	monitor, 
			ISVDBIndexOperation op, 
			boolean 			sync);
}
