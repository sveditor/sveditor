package net.sf.sveditor.core.db.index;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBIndexOperation {
	
//	void pre_operation(ISVDBIndex index);

	/**
	 * Execute the operation
	 * 
	 * @param index
	 */
	void index_operation(IProgressMonitor monitor, ISVDBIndex index);

//	int operation_depth();
	
//	void post_operation(ISVDBIndex index);
	

}
