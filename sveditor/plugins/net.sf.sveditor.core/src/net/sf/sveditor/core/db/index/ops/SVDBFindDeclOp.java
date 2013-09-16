package net.sf.sveditor.core.db.index.ops;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;

public class SVDBFindDeclOp implements ISVDBIndexOperation {
	private String								fName;
	private ISVDBFindNameMatcher				fMatcher;
	private List<SVDBDeclCacheItem>				fResults;
	
	public SVDBFindDeclOp(String name, ISVDBFindNameMatcher matcher) {
		fName = name;
		fMatcher = matcher;
		fResults = new ArrayList<SVDBDeclCacheItem>();
	}

	@Override
	public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(new NullProgressMonitor(), fName, fMatcher);
		
		fResults.addAll(result);
	}
	
	public static List<SVDBDeclCacheItem> op(ISVDBIndexOperationRunner runner, String name, ISVDBFindNameMatcher matcher, boolean sync) {
		SVDBFindDeclOp op = new SVDBFindDeclOp(name, matcher);
	
		runner.execOp(new NullProgressMonitor(), op, sync);

		return op.fResults;
	}

}
