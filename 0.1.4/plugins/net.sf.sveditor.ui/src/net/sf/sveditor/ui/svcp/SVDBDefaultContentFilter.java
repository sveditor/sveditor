package net.sf.sveditor.ui.svcp;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

public class SVDBDefaultContentFilter extends ViewerFilter {

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		
		if (element instanceof SVDBItem &&
				((SVDBItem)element).getType() == SVDBItemType.Marker) {
			return false;
		}
		
		return true;
	}

}
