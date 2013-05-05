package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFindOperation implements ISVDBIndexOperation {
	private List<SVDBDeclCacheItem>				fResult;
	private String								fName;
	private ISVDBFindNameMatcher				fMatcher;
	
	public SVDBFindOperation() {
		fResult = new ArrayList<SVDBDeclCacheItem>();
	}

	static List<SVDBDeclCacheItem> find(
			IProgressMonitor			monitor,
			ISVDBIndexOperationRunner 	runner, 
			String						name,
			ISVDBFindNameMatcher		matcher,
			boolean						sync) {
		SVDBFindOperation op = new SVDBFindOperation();
		
		runner.execOp(monitor, op, sync);
		
		return op.fResult;
	}

	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(monitor, fName, fMatcher);
		fResult.addAll(result);
	}

}
