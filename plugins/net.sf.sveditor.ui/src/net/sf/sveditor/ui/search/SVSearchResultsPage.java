package net.sf.sveditor.ui.search;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.search.ui.text.AbstractTextSearchViewPage;

public class SVSearchResultsPage extends AbstractTextSearchViewPage implements IAdaptable {
	private SVSearchTreeContentProvider				fContentProvider;
	
	@Override
	protected void elementsChanged(Object[] objects) {
		if (fContentProvider != null) {
			fContentProvider.elementsChanged(objects);
		}
	}

	@Override
	protected void clear() {
		if (fContentProvider != null) {
			fContentProvider.clear();
		}
	}

	@Override
	protected void configureTreeViewer(TreeViewer viewer) {
		fContentProvider = new SVSearchTreeContentProvider(this, viewer);
		viewer.setLabelProvider(new SVSearchLabelProvider());
		viewer.setContentProvider(fContentProvider);
	}

	@Override
	protected void configureTableViewer(TableViewer viewer) {
		System.out.println("configureTableViewer");
	}

	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		// TODO Auto-generated method stub
		return null;
	}

}
