package net.sf.sveditor.core.db.refs;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBRefFinder {

	/**
	 * Locate the matches referred to by 'item'
	 * 
	 * @param item
	 * @return
	 */
	List<SVDBRefItem> findReferences(
			IProgressMonitor 		monitor, 
			ISVDBRefSearchSpec		ref_spec,
			ISVDBRefMatcher			ref_matcher);
	
}
