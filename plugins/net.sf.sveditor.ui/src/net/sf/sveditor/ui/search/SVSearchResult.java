package net.sf.sveditor.ui.search;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.text.AbstractTextSearchResult;
import org.eclipse.search.ui.text.IEditorMatchAdapter;
import org.eclipse.search.ui.text.IFileMatchAdapter;
import org.eclipse.search.ui.text.Match;
import org.eclipse.ui.IEditorPart;

public class SVSearchResult extends AbstractTextSearchResult implements IEditorMatchAdapter {
	private SVSearchQuery		fQuery;
	
	public SVSearchResult(SVSearchQuery query) {
		fQuery = query;
		/*
		fLabel = label;
		fTooltip = tooltip;
		 */
	}

	public String getLabel() {
		return "SystemVerilog Search";
	}

	public String getTooltip() {
		return "tooltip";
	}

	public ImageDescriptor getImageDescriptor() {
		// TODO Auto-generated method stub
		return null;
	}

	public ISearchQuery getQuery() {
		return fQuery;
	}

	@Override
	public IEditorMatchAdapter getEditorMatchAdapter() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IFileMatchAdapter getFileMatchAdapter() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean isShownInEditor(Match match, IEditorPart editor) {
		// TODO Auto-generated method stub
		return false;
	}

	public Match[] computeContainedMatches(AbstractTextSearchResult result,
			IEditorPart editor) {
		// TODO Auto-generated method stub
		return null;
	}

}
