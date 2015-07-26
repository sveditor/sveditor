package net.sf.sveditor.ui.wizards.project;

import java.io.File;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;

public class ScopedFileSelectionDialog extends Dialog implements ITreeContentProvider {
	private String 				fPathStr;
	private TreeViewer			fTreeViewer;
	private File				fProject;
	
	
	public ScopedFileSelectionDialog(Shell shell, File project) {
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
		
		fTreeViewer.setContentProvider(this);
//		fTreeViewer.addFilter(new ViewerFilter() {
//
//			@Override
//			public boolean select(Viewer viewer, Object parentElement,
//					Object element) {
//				return (element instanceof IResource && 
//						((IResource)element).getProject().equals(fProject));
//			}
//		});
		fTreeViewer.setLabelProvider(fLabelProvider);
		fTreeViewer.setInput(this);
		
		fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
				if (sel.getFirstElement() != null) {
					File file = (File)sel.getFirstElement();
					fPathStr = file.getAbsolutePath().substring(fProject.getAbsolutePath().length());
				}
			}
		});
		
		fTreeViewer.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				buttonPressed(IDialogConstants.OK_ID);
			}
		});
		

		return fTreeViewer.getControl();
	}

	@Override
	public void dispose() { }

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }

	@Override
	public Object[] getElements(Object inputElement) {
		return new File[] {fProject};
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof File && ((File)parentElement).isDirectory()) {
			return ((File)parentElement).listFiles();
		}
		
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof File) {
			return ((File)element).getParentFile();
		}
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof File && ((File)element).isDirectory()) {
			return ((File)element).listFiles().length > 0;
		}
		return false;
	}
	
	private LabelProvider 		fLabelProvider = new LabelProvider() {

		@Override
		public Image getImage(Object element) {
			// TODO Auto-generated method stub
			return super.getImage(element);
		}

		@Override
		public String getText(Object element) {
			if (element instanceof File) {
				return ((File)element).getName();
			}

			return super.getText(element);
		}
		
	};
	
}
