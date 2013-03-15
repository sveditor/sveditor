package net.sf.sveditor.ui.wizards.templates;

import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.CheckboxCellEditor;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ComboBoxCellEditor;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;

public class SVTemplateParametersPage2 extends WizardPage {
	
	private TreeViewer					fParametersTree;
	
	public SVTemplateParametersPage2() {
		super("Parameters");
	}
	
	public void createControl(Composite parent) {
		Group c = new Group(parent, SWT.NONE);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout());
		c.setText("Parameters");

		fParametersTree = new TreeViewer(c, SWT.BORDER+SWT.FULL_SELECTION);
		fParametersTree.getTree().setLinesVisible(true);
		fParametersTree.getTree().setHeaderVisible(true);
		fParametersTree.getTree().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
	
		TreeViewerColumn column;
		
		column = new TreeViewerColumn(fParametersTree, SWT.NONE);
		column.getColumn().setWidth(200);
		column.getColumn().setMoveable(false);
		column.getColumn().setText("Name");
		column.setLabelProvider(new ColumnLabelProvider() {

			@Override
			public String getText(Object element) {
				return "Cell " + element;
			}
		});
		
		fParametersTree.setContentProvider(new ITreeContentProvider() {
			
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
			}
			
			public void dispose() {
			}
			
			public boolean hasChildren(Object element) {
				// TODO Auto-generated method stub
				return false;
			}
			
			public Object getParent(Object element) {
				return null;
			}
			
			public Object[] getElements(Object inputElement) {
				return new String[] {"Elem1", "Elem2", "Elem3", "Elem4"};
			}
			
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		});

		column = new TreeViewerColumn(fParametersTree, SWT.NONE);
		column.getColumn().setWidth(200);
		column.getColumn().setMoveable(false);
		column.getColumn().setText("Type");
		column.setLabelProvider(new ColumnLabelProvider() {

			@Override
			public String getText(Object element) {
				return "Cell " + element;
			}
		});
		
		fParametersTree.setContentProvider(new ITreeContentProvider() {
			
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
			}
			
			public void dispose() {
			}
			
			public boolean hasChildren(Object element) {
				// TODO Auto-generated method stub
				return false;
			}
			
			public Object getParent(Object element) {
				return null;
			}
			
			public Object[] getElements(Object inputElement) {
				return new String[] {"Elem1", "Elem2", "Elem3", "Elem4"};
			}
			
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		});
		
		column = new TreeViewerColumn(fParametersTree, SWT.NONE);
		column.getColumn().setWidth(200);
		column.getColumn().setMoveable(false);
		column.getColumn().setText("Value");
		column.setLabelProvider(new ColumnLabelProvider() {

			@Override
			public String getText(Object element) {
				return "Cell " + element;
			}
		});
		
		fParametersTree.setContentProvider(new ITreeContentProvider() {
			
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
			}
			
			public void dispose() {
			}
			
			public boolean hasChildren(Object element) {
				// TODO Auto-generated method stub
				return false;
			}
			
			public Object getParent(Object element) {
				return null;
			}
			
			public Object[] getElements(Object inputElement) {
				return new Object[] {"Elem1", "Elem2", "Elem3", "Elem4"};
			}
			
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		});
		
		final CheckboxCellEditor check_editor = new CheckboxCellEditor(fParametersTree.getTree());
		final TextCellEditor text_editor = new TextCellEditor(fParametersTree.getTree());
		final ComboBoxCellEditor combo_editor = new ComboBoxCellEditor(fParametersTree.getTree(), 
				new String[] { "A", "B", "C" });
		
		column.setEditingSupport(new EditingSupport(fParametersTree) {
			
			@Override
			protected void setValue(Object element, Object value) {
				System.out.println("setValue: " + element + " " + value);
				// TODO Auto-generated method stub
				
			}
			
			@Override
			protected Object getValue(Object element) {
				if (element.toString().equals("Elem1")) {
					return 1;
				} else {
					return element;
				}
			}
			
			@Override
			protected CellEditor getCellEditor(Object element) {
				System.out.println("getCellEditor: " + element);
				
				if (element.toString().equals("Elem1")) {
					return combo_editor;
				} else {
					return text_editor;
				}
			}
			
			@Override
			protected boolean canEdit(Object element) {
				// TODO Auto-generated method stub
				return true;
			}
		});

		fParametersTree.setInput(new Object());
		
		setControl(c);
	}

}
