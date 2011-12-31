package net.sf.sveditor.ui.compare;

import org.eclipse.compare.CompareConfiguration;
import org.eclipse.compare.IViewerCreator;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Composite;

public class SVCompareViewerCreator implements IViewerCreator {

	public SVCompareViewerCreator() {
		// TODO Auto-generated constructor stub
	}

	public Viewer createViewer(Composite parent, CompareConfiguration config) {
		return new SVCompareViewer(parent, config);
	}

}
