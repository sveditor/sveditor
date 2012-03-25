package net.sf.sveditor.ui.prop_pages;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
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

public class ProjectDirectoryDialog extends Dialog {
	private String 				fPathStr;
	private TreeViewer			fTreeViewer;
	private IProject			fProject;
	
	
	public ProjectDirectoryDialog(Shell shell, IProject project) {
		super(shell);
		fProject = project;
	}

	public String getPath() {
		return fPathStr;
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
				return (element instanceof IContainer && 
						((IResource)element).getProject().equals(fProject));
			}
		});
		fTreeViewer.setLabelProvider(new WorkbenchLabelProvider());
		fTreeViewer.setInput(ResourcesPlugin.getWorkspace());
		
		fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
				if (sel.getFirstElement() != null) {
					fPathStr = ((IContainer)sel.getFirstElement()).getFullPath().toOSString();
				}
			}
		});
		

		return fTreeViewer.getControl();
	}
}
