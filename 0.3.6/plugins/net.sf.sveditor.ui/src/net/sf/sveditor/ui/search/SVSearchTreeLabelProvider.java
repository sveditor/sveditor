package net.sf.sveditor.ui.search;

import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.StyledString;

public class SVSearchTreeLabelProvider extends SVTreeLabelProvider {
	
	public SVSearchTreeLabelProvider() {
		fShowFunctionRetType = false;
	}

	public StyledString getStyledText(Object element) {
		// TODO Auto-generated method stub
		return super.getStyledText(element);
	}
}
