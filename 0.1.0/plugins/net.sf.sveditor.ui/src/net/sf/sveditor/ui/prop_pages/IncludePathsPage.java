package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

public class IncludePathsPage implements ISVProjectPropsPage,
	IStructuredContentProvider, ILabelProvider {
	private ListViewer					fIncludePathViewer;
	private SVProjectFileWrapper		fProjectWrapper;
	private List<SVDBPath>				fIncludePaths;
	private Button						fAdd;
	private Button						fRemove;
	private Button						fEdit;

	public IncludePathsPage() {
		fIncludePaths = new ArrayList<SVDBPath>();
	}
	

	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
		
		fIncludePaths.clear();
		for (SVDBPath p : fProjectWrapper.getIncludePaths()) {
			fIncludePaths.add(p.duplicate());
		}
	}

	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(2, false));
		
		fIncludePathViewer = new ListViewer(frame, SWT.BORDER);
		fIncludePathViewer.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fIncludePathViewer.setContentProvider(this);
		fIncludePathViewer.setLabelProvider(this);
		fIncludePathViewer.setInput(fIncludePaths);
		fIncludePathViewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelection();
			}
		});
		
		Composite button_bar = new Composite(frame, SWT.NONE);
		button_bar.setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, false, true));
		button_bar.setLayout(new GridLayout(1, true));
		
		fAdd = new Button(button_bar, SWT.PUSH);
		fAdd.setText("Add");
		fAdd.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fAdd.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}
			public void widgetSelected(SelectionEvent e) {
				add();
			}
		});

		fEdit = new Button(button_bar, SWT.PUSH);
		fEdit.setText("Edit");
		fEdit.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fEdit.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				edit();
			}
		});

		fRemove = new Button(button_bar, SWT.PUSH);
		fRemove.setText("Remove");
		fRemove.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fRemove.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				remove();
			}
		});


		updateSelection();
		
		return frame;
	}
	
	private void add() {
		AddDirectoryPathDialog dlg = new AddDirectoryPathDialog(fAdd.getShell());
		
		if (dlg.open() == Window.OK) {
			SVDBPath path = new SVDBPath(dlg.getPath(), false);
			fIncludePaths.add(path);
			fIncludePathViewer.refresh();
		}
	}
	
	private void edit() {
		IStructuredSelection sel = (IStructuredSelection)fIncludePathViewer.getSelection();
		SVDBPath elem = (SVDBPath)sel.getFirstElement();
		
		AddDirectoryPathDialog dlg = new AddDirectoryPathDialog(fAdd.getShell());
		dlg.setInitialPath(elem.getPath());
		
		if (dlg.open() == Window.OK) {
			elem.setPath(dlg.getPath());
			fIncludePathViewer.refresh();
		}
	}
	
	private void remove() {
		IStructuredSelection sel = (IStructuredSelection)fIncludePathViewer.getSelection();
		
		for (Object sel_o : sel.toList()) {
			fIncludePaths.remove(sel_o);
		}
		
		fIncludePathViewer.refresh();
	}
	
	private void updateSelection() {
		IStructuredSelection sel = 
			(IStructuredSelection)fIncludePathViewer.getSelection();
		
		fAdd.setEnabled(true);
		if (sel.getFirstElement() == null) {
			fRemove.setEnabled(false);
			fEdit.setEnabled(false);
		} else {
			if (sel.size() == 1) {
				fEdit.setEnabled(true);
			} else {
				fEdit.setEnabled(false);
			}
			fRemove.setEnabled(true);
		}
	}

	public Image getIcon() {
		return SVUiPlugin.getImage("/icons/edecl16/include_obj.gif");
	}

	public String getName() {
		return "Include Paths";
	}

	public void perfomOk() {
		fProjectWrapper.getIncludePaths().clear();
		
		for (SVDBPath p : fIncludePaths) {
			fProjectWrapper.getIncludePaths().add(p.duplicate());
		}
	}

	public Object[] getElements(Object inputElement) {
		return fIncludePaths.toArray();
	}

	public Image getImage(Object element) {
		return null;
	}


	public String getText(Object element) {
		if (element instanceof SVDBPath) {
			return ((SVDBPath)element).getPath();
		}
		return null;
	}


	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {}
	public void dispose() {}
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
	public void addListener(ILabelProviderListener listener) {}
	
}
