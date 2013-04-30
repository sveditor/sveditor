package net.sf.sveditor.svt.editor.wizards;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class WorkspaceDirectoryDialog extends Dialog {
	private TreeViewer			fTreeViewer;
	private IContainer			fContainer;
	
	
	public WorkspaceDirectoryDialog(Shell shell, IContainer container) {
		super(shell);
		fContainer = container;
	}

	public IContainer getContainer() {
		return fContainer;
	}
	
	@Override
	protected Control createDialogArea(Composite p) {
		Composite parent = new Composite(p, SWT.NONE);
		parent.setLayout(new GridLayout(1, true));
		
		fTreeViewer = new TreeViewer(parent);
		
		GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.widthHint = 300;
		gd.heightHint = 300;
		fTreeViewer.getControl().setLayoutData(gd);
		fTreeViewer.setAutoExpandLevel(2);
		
		fTreeViewer.setContentProvider(new WorkbenchContentProvider());
		fTreeViewer.addFilter(new ViewerFilter() {

			@Override
			public boolean select(Viewer viewer, Object parentElement,
					Object element) {
				return (element instanceof IContainer);
			}
		});
		fTreeViewer.setLabelProvider(new WorkbenchLabelProvider());
		fTreeViewer.setInput(ResourcesPlugin.getWorkspace());
		
		fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
				if (sel.getFirstElement() != null) {
					fContainer = (IContainer)sel.getFirstElement();
				}
			}
		});
		
		if (fContainer != null) {
			fTreeViewer.setSelection(new StructuredSelection(fContainer), true);
		}
		

		return fTreeViewer.getControl();
	}
}
