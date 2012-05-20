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
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Text;

public class TemplateParametersTableViewer extends TableViewer {
	private List<TemplateParameter>				fParameters;
	private List<ModifyListener>				fModifyListeners;
	private String								fSourceFolderStr = "";
	private TemplateParameter					fActiveParameter;
	
	public TemplateParametersTableViewer(Composite parent) {
		super(parent);
		
		fParameters = new ArrayList<TemplateParameter>();
		fModifyListeners = new ArrayList<ModifyListener>();
		
		getTable().setHeaderVisible(true);
		
		TableViewerColumn err = new TableViewerColumn(this, SWT.LEFT, 0);
		err.getColumn().setText("Name");
		err.getColumn().setWidth(100);
		
		TableViewerColumn name = new TableViewerColumn(this, SWT.LEFT, 1);
		name.getColumn().setText("Type");
		name.getColumn().setWidth(100);
		
		TableViewerColumn value = new TableViewerColumn(this, SWT.LEFT, 2);
		value.getColumn().setText("Value");
		value.getColumn().setWidth(100);
		value.setEditingSupport(new ValueEditingSupport(getTable(), this));
		
		setColumnProperties(new String[] {"name", "type", "value"});
		
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
	
	public List<TemplateParameter> getParameters() {
		return fParameters;
	}
	
	public void setSourceFolder(String src_folder) {
		fSourceFolderStr = src_folder;
	}
	
	public void addModifyListener(ModifyListener l) {
		fModifyListeners.add(l);
	}
	
	private void triggerListeners() {
		Event ev = new Event();
		ev.widget = getTable();
		ModifyEvent e = new ModifyEvent(ev);
		e.widget = this.getTable();
		for (ModifyListener l : fModifyListeners) {
			l.modifyText(e);
		}
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
			TemplateParameter p = (TemplateParameter)element;
			
			switch (columnIndex) {
				case 0:
					ret = p.getName();
					break;
					
				case 1:
					ret = p.getTypeName();
					break;
					
				case 2:
					ret = p.getValue();
					break;
			}
			return ret;
		}
	};
	private ITableLabelProvider labelProvider = new ParamLabelProvider();
	
	private class ValueEditingSupport extends EditingSupport {
		private ComboBoxCellEditor			fRestrictedIdEditor;
		private TextCellEditor				fIdEditor;
		private TextCellEditor				fClassEditor;
		
		public ValueEditingSupport(Composite parent, ColumnViewer viewer) {
			super(viewer);
			
			fRestrictedIdEditor = new ComboBoxCellEditor(parent, new String[] {}, SWT.READ_ONLY);
			fIdEditor = new TextCellEditor(parent, SWT.NONE);
			fClassEditor = new TextCellEditor(parent, SWT.SEARCH+SWT.ICON_SEARCH+SWT.CANCEL+SWT.ICON_CANCEL);
			
			final Text t = (Text)fClassEditor.getControl();
			t.addListener(SWT.DefaultSelection, new Listener() {
				
				public void handleEvent(Event event) {
					ClassBrowseDialog d = new ClassBrowseDialog(
							t.getShell(), fSourceFolderStr, 
							fActiveParameter.getExtFrom());
					
					if (d.open() == Dialog.OK) {
						t.setText(d.getSelectedClass());
					}
				}
			});
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			CellEditor ret = null;
			TemplateParameter p = (TemplateParameter)element;
			
			fActiveParameter = p;
			
			if (p.getType() == TemplateParameterType.ParameterType_Id) {
				System.out.println("ID");
				if (p.getValues().size() > 0) {
					ret = fRestrictedIdEditor;
					((CCombo)ret.getControl()).setItems(
							p.getValues().toArray(new String[p.getValues().size()]));
				} else {
					ret = fIdEditor;
				}
			} else if (p.getType() == TemplateParameterType.ParameterType_Class) {
				System.out.println("Class Editor");
				ret = fClassEditor;
			}
			
			System.out.println("ret=" + ret);
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
				return p.getValue();
			}
			return "";
		}

		@Override
		protected void setValue(Object element, Object value) {
			TemplateParameter p = (TemplateParameter)element;
			if (p.getType() == TemplateParameterType.ParameterType_Class) {
				p.setValue(value.toString());
			} else {
				if (p.getValues().size() > 0) {
					CCombo c = (CCombo)fRestrictedIdEditor.getControl();
					p.setValue(c.getText());
				} else {
					p.setValue(value.toString());
				}
			}
			refresh();
			triggerListeners();
		}
	}
	
}
