package net.sf.sveditor.core.db.refs;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBRefFinder {

	/**
	 * Locate the matches referred to by 'item'
	 * 
	 * @param item
	 * @return
	 */
	void findReferences(
			IProgressMonitor 		monitor, 
			ISVDBRefSearchSpec		ref_spec,
			ISVDBRefVisitor			ref_matcher);
	
}
