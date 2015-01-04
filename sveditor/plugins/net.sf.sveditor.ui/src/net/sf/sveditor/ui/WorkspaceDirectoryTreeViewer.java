package net.sf.sveditor.ui;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class WorkspaceDirectoryTreeViewer extends TreeViewer {
	
	public WorkspaceDirectoryTreeViewer(Composite parent, int style) {
		super(parent, style);

		setContentProvider(new WorkbenchContentProvider());
		addFilter(new ViewerFilter() {

			@Override
			public boolean select(Viewer viewer, Object parentElement,
					Object element) {
				return (element instanceof IContainer);
			}
		});
		setLabelProvider(new WorkbenchLabelProvider());
		setInput(ResourcesPlugin.getWorkspace());
	}
	
}
