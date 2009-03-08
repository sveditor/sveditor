package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.project.SVDBPath;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;

public class SVProjectPathsPage {
	
	private List<SVDBPath> 			fPathList = new ArrayList<SVDBPath>();
	private ListViewer				fPathListViewer;
	private Button					fRemoveButton;
	private Button					fEditButton;
	private static String			fInitialDir = null;

	public void init(List<SVDBPath> path_list) {
		fPathList.clear();
		fPathList.addAll(path_list);
		
		if (fPathListViewer != null) {
			fPathListViewer.refresh();
		}
	}
	
	public List<SVDBPath> getPathList() {
		return fPathList;
	}
	
	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(2, false));
		
		Composite list_c = new Composite(frame, SWT.NONE);
		list_c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		list_c.setLayout(new GridLayout(1, true));
		
		fPathListViewer = new ListViewer(list_c);
		fPathListViewer.setContentProvider(contentProvider);		
		fPathListViewer.setLabelProvider(labelProvider);
		fPathListViewer.setInput(fPathList);
		fPathListViewer.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fPathListViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(SelectionChangedEvent event) {
				updateSelection(event.getSelection());
			}
		});
		
		Composite button_c = new Composite(frame, SWT.NO_TRIM);
		button_c.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false));
		button_c.setLayout(new GridLayout(1, true));

		Button add = new Button(button_c, SWT.PUSH);
		add.setText("Add");
		add.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		add.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				addPath();
			}
		});
		
		fRemoveButton = new Button(button_c, SWT.PUSH);
		fRemoveButton.setText("Remove");
		fRemoveButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fRemoveButton.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				removePath();
			}
		});
		
		fEditButton = new Button(button_c, SWT.PUSH);
		fEditButton.setText("Edit");
		fEditButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fEditButton.addSelectionListener(new SelectionListener() {

			public void widgetDefaultSelected(SelectionEvent e) {}

			public void widgetSelected(SelectionEvent e) {
				editPath();
			}
			
		});
		
		updateSelection(null);
		
		Dialog.applyDialogFont(frame);
		
		return frame;
	}
	
	private void updateSelection(ISelection sel_i) {
		IStructuredSelection sel;
		
		if (sel_i != null) {
			sel = (IStructuredSelection)sel_i;
		} else {
			sel = (IStructuredSelection)fPathListViewer.getSelection();
		}
		
		if (sel != null && sel.toList().size() > 0) {
			fRemoveButton.setEnabled(true);
			
			if (sel.toList().size() == 1) {
				fEditButton.setEnabled(true);
			} else {
				fEditButton.setEnabled(false);
			}
		} else {
			fRemoveButton.setEnabled(false);
			fEditButton.setEnabled(false);
		}
	}
	
	private void addPath() {
		DirectoryDialog dlg = new DirectoryDialog(fRemoveButton.getShell());
		if (fInitialDir != null) {
			dlg.setFilterPath(fInitialDir);
		}
		
		String selectedDirectory = dlg.open();
		
		if (selectedDirectory != null) {
			// Add a new entry
			fInitialDir = selectedDirectory;
			
			SVDBPath p = new SVDBPath(selectedDirectory, false, false);
			fPathList.add(p);
			fPathListViewer.refresh();
		}
	}
	
	private void removePath() {
		IStructuredSelection sel = (IStructuredSelection)fPathListViewer.getSelection();
		
		if (sel != null) {
			for (Object obj : sel.toList()) {
				fPathList.remove(obj);
			}
		}
		
		fPathListViewer.refresh();
		fPathListViewer.setSelection(null);
	}
	
	private void editPath() {
		IStructuredSelection sel = (IStructuredSelection)fPathListViewer.getSelection();

		if (sel != null) {
			SVDBPath p = (SVDBPath)sel.getFirstElement();
			DirectoryDialog dlg = new DirectoryDialog(fRemoveButton.getShell());
			
			dlg.setFilterPath(p.getPath());
			
			String selectedDirectory = dlg.open();
			
			if (selectedDirectory != null) {
				p.setPath(selectedDirectory);
				
				fInitialDir = selectedDirectory;
				
				fPathListViewer.refresh();
			}
		}
	}

	private IStructuredContentProvider contentProvider = new IStructuredContentProvider() {

		public Object[] getElements(Object inputElement) {
			if (inputElement instanceof List<?>) {
				return ((List<?>)inputElement).toArray();
			}
			return null;
		}

		public void dispose() {}

		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
		
	};
	
	private IBaseLabelProvider labelProvider = new LabelProvider() {

		@Override
		public String getText(Object element) {
			if (element instanceof SVDBPath) {
				return ((SVDBPath)element).getPath();
			}
			return super.getText(element);
		}
		
	};

}
