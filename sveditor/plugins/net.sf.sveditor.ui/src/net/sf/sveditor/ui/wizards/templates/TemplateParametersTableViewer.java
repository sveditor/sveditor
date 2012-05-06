package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.templates.TemplateParameter;
import net.sf.sveditor.core.templates.TemplateParameterType;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.ComboBoxCellEditor;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CCombo;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;

public class TemplateParametersTableViewer extends TableViewer {
	private List<TemplateParameter>				fParameters;
	private String								fEditValue;
	
	public TemplateParametersTableViewer(Composite parent) {
		super(parent);
		
		fParameters = new ArrayList<TemplateParameter>();
		
		getTable().setHeaderVisible(true);
		
		TableViewerColumn err = new TableViewerColumn(this, SWT.LEFT, 0);
		err.getColumn().setText("Status");
		err.getColumn().setWidth(50);
		
		TableViewerColumn name = new TableViewerColumn(this, SWT.LEFT, 1);
		name.getColumn().setText("Name");
		name.getColumn().setWidth(100);
		
		TableViewerColumn value = new TableViewerColumn(this, SWT.LEFT, 2);
		value.getColumn().setText("Value");
		value.getColumn().setWidth(100);
		value.setEditingSupport(new ValueEditingSupport(getTable(), this));
		
		setColumnProperties(new String[] {"status", "name", "value"});
		
		setContentProvider(contentProvider);
		setLabelProvider(labelProvider);
	}
	
	public void setParameters(List<TemplateParameter> params) {
		fParameters = new ArrayList<TemplateParameter>();
		if (params != null) {
			for (TemplateParameter p : params) {
				fParameters.add(p.duplicate());
			}
		}
		
		setInput(fParameters);
	}

	IStructuredContentProvider contentProvider = new IStructuredContentProvider() {
		
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
		public void dispose() {}
		
		public Object[] getElements(Object inputElement) {
			return fParameters.toArray();
		}
	};

	private class ParamLabelProvider extends LabelProvider implements ITableLabelProvider {

		public Image getColumnImage(Object element, int columnIndex) {
			Image ret = null;
			
			switch (columnIndex) {
			
			}
			
			return ret;
		}

		public String getColumnText(Object element, int columnIndex) {
			String ret = "" + columnIndex;
			
			switch (columnIndex) {
				case 1:
					ret = ((TemplateParameter)element).getName();
					break;
					
				case 2:
					ret = ((TemplateParameter)element).getValue();
					System.out.println("getColumnText: " + ret);
					break;
			}
			return ret;
		}
	};
	private ITableLabelProvider labelProvider = new ParamLabelProvider();
	
	private class ValueEditingSupport extends EditingSupport {
		private ComboBoxCellEditor			fRestrictedIdEditor;
		private TextCellEditor				fIdEditor;
		private ComboBoxCellEditor			fClassEditor;
		
		public ValueEditingSupport(Composite parent, ColumnViewer viewer) {
			super(viewer);
			
			fRestrictedIdEditor = new ComboBoxCellEditor(parent, new String[] {}, SWT.READ_ONLY);
			fIdEditor = new TextCellEditor(parent, SWT.NONE);
			fClassEditor = new ComboBoxCellEditor(parent, new String[] {});
			
			final CCombo c = (CCombo)fClassEditor.getControl(); 
			c.addSelectionListener(new SelectionListener() {
				public void widgetDefaultSelected(SelectionEvent e) {}
				
				public void widgetSelected(SelectionEvent e) {
					System.out.println("Selected: " + e);
					if (c.getText().equals("Browse...")) {
						ClassBrowseDialog d = new ClassBrowseDialog(c.getShell());
						
						if (d.open() == Dialog.OK) {
							c.setItem(0, "A");
						} else {
						}
						c.select(0);
						e.doit = false;
					}
				}
			});
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			CellEditor ret = null;
			TemplateParameter p = (TemplateParameter)element;
			
			if (p.getType() == TemplateParameterType.ParameterType_Id) {
				if (p.getValues().size() > 0) {
					ret = fRestrictedIdEditor;
					((CCombo)ret.getControl()).setItems(
							p.getValues().toArray(new String[p.getValues().size()]));
				} else {
					ret = fIdEditor;
				}
			} else if (p.getType() == TemplateParameterType.ParameterType_Class) {
				ret = fClassEditor;
				((CCombo)ret.getControl()).setItems(
						new String[] {p.getValue(), "Browse..."});
			}
			
			return ret;
		}

		@Override
		protected boolean canEdit(Object element) {
			return true;
		}

		@Override
		protected Object getValue(Object element) {
			TemplateParameter p = (TemplateParameter)element;
			
			if (p.getType() == TemplateParameterType.ParameterType_Id) {
				if (p.getValues().size() > 0) {
					return p.getValues().indexOf(p.getValue());
				} else {
					return p.getValue();
				}
			} else if (p.getType() == TemplateParameterType.ParameterType_Class) {
				return new Integer(0);
			}
			return "";
		}

		@Override
		protected void setValue(Object element, Object value) {
			TemplateParameter p = (TemplateParameter)element;
			System.out.println("setValue: " + value);
			if (p.getType() == TemplateParameterType.ParameterType_Class) {
				int idx = (Integer)value;
				CCombo c = (CCombo)fClassEditor.getControl();
				
				p.setValue(c.getText());
			} else {
				p.setValue(value.toString());
			}
			refresh();
		}
	}
	
}
