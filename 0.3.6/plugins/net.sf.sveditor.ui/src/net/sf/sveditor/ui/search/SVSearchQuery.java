package net.sf.sveditor.ui.search;

import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBSearchEngine;
import net.sf.sveditor.core.db.search.SVDBSearchSpecification;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.ISearchResult;
import org.eclipse.search.ui.text.AbstractTextSearchResult;

public class SVSearchQuery implements ISearchQuery {
	private SVSearchResult				fSearchResult;
	private SVDBSearchSpecification		fSearchSpec;
	private ISVDBIndexIterator			fSearchContext;
	private String						fLabel;
	
	public SVSearchQuery(
			ISVDBIndexIterator			search_ctxt,
			SVDBSearchSpecification		search_spec) {
		fSearchContext 	= search_ctxt;
		fSearchSpec 	= search_spec;
		updateLabel();
	}

	public IStatus run(IProgressMonitor monitor) throws OperationCanceledException {
		AbstractTextSearchResult textResult= (AbstractTextSearchResult) getSearchResult();
		textResult.removeAll();

		/*
		Pattern searchPattern= getSearchPattern();
		boolean searchInBinaries= !isScopeAllFileTypes();

		TextSearchResultCollector collector= new TextSearchResultCollector(textResult, isFileNameSearch(), searchInBinaries);
		return TextSearchEngine.create().search(fScope, collector, searchPattern, monitor);
		 */
		search(monitor);
		
		// TODO Auto-generated method stub
		return Status.OK_STATUS;
	}
	
	private void updateLabel() {
		String type = "";
		switch (fSearchSpec.getSearchType()) {
			case Field: type = "Field "; break;
			case Method: type = "Method "; break;
			case Package: type = "Package "; break;
			case Type: type = "Type "; break;
		}
		
		fLabel = type + fSearchSpec.getExpr();
		if (fSearchResult != null) {
			fLabel += " - " + fSearchResult.getMatchCount() + " matches";
		}
	}
	
	private void search(IProgressMonitor monitor) throws OperationCanceledException {
		AbstractTextSearchResult result = (AbstractTextSearchResult) getSearchResult();
		SVDBSearchEngine engine = new SVDBSearchEngine(fSearchContext);
		List<SVDBItem> results = engine.find(fSearchSpec, monitor);
		
		for (SVDBItem it : results) {
			result.addMatch(new SVSearchMatch(it));
		}
	}

	public String getLabel() {
		return fLabel;
	}

	public boolean canRerun() {
		// TODO Auto-generated method stub
		return false;
	}

	public boolean canRunInBackground() {
		return true;
	}

	public ISearchResult getSearchResult() {
		if (fSearchResult == null) {
			fSearchResult = new SVSearchResult(this);
		}
		
		return fSearchResult;
	}
}
