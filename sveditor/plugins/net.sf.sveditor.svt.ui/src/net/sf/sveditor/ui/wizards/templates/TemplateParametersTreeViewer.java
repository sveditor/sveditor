package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.svt.core.templates.ITemplateParameterProvider;
import net.sf.sveditor.svt.core.templates.TemplateParameter;
import net.sf.sveditor.svt.core.templates.TemplateParameterBase;
import net.sf.sveditor.svt.core.templates.TemplateParameterComposite;
import net.sf.sveditor.svt.core.templates.TemplateParameterGroup;
import net.sf.sveditor.svt.core.templates.TemplateParameterSet;
import net.sf.sveditor.svt.core.templates.TemplateParameterType;
import net.sf.sveditor.svt.ui.SvtUiPlugin;

import org.eclipse.jface.layout.TreeColumnLayout;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewer;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.ComboBoxCellEditor;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.ICellEditorValidator;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;

public class TemplateParametersTreeViewer extends TreeViewer {
	private TemplateParameterSet				fParameters;
	private List<ModifyListener>				fModifyListeners;
	private TextCellEditor						fTextCellEditor;
	private TextCellEditor						fIntCellEditor;
	private ComboBoxCellEditor					fComboBoxCellEditor;
	private Composite							fRealParent;
	
	private TemplateParametersTreeViewer(Composite real_parent, int style) {
		super(real_parent, style);
		fRealParent = real_parent;
	}
	
	public TemplateParametersTreeViewer(Composite parent) {
		this(new Composite(parent, SWT.NONE), SWT.BORDER+SWT.FULL_SELECTION);
		
		fModifyListeners = new ArrayList<ModifyListener>();
	
		getTree().setLinesVisible(true);
		getTree().setHeaderVisible(true);
		
		addFilter(hiddenItemsFilter);
		
		TreeViewerColumn column;
		TreeColumnLayout layout = new TreeColumnLayout();
		
		column = new TreeViewerColumn(this, SWT.NONE);
		column.getColumn().setWidth(200);
		column.getColumn().setMoveable(false);
		column.getColumn().setText("Name");
		column.setLabelProvider(nameLabelProvider);
		layout.setColumnData(column.getColumn(), new ColumnWeightData(30));
		
		// TODO: label provider

		column = new TreeViewerColumn(this, SWT.NONE);
		column.getColumn().setWidth(200);
		column.getColumn().setMoveable(false);
		column.getColumn().setText("Type");
		column.setLabelProvider(typeLabelProvider);
		layout.setColumnData(column.getColumn(), new ColumnWeightData(30));
		
		column = new TreeViewerColumn(this,  SWT.NONE);
		column.getColumn().setWidth(200);
		column.getColumn().setMoveable(false);
		column.getColumn().setText("Value");
		column.setLabelProvider(valueLabelProvider);
		layout.setColumnData(column.getColumn(), new ColumnWeightData(30));
		
		
		fRealParent.setLayout(layout);
		
		fTextCellEditor = new TextCellEditor(getTree());
		fIntCellEditor = new TextCellEditor(getTree());
		fIntCellEditor.setValidator(new ICellEditorValidator() {
			public String isValid(Object value) {
				// TODO: validate value
				return null;
			}
		});
		
		fComboBoxCellEditor = new ComboBoxCellEditor(getTree(),
				new String[] {}, SWT.READ_ONLY);
		
		column.setEditingSupport(new ValueEditingSupport(this));
	
		/*
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
		 */
		
		setContentProvider(contentProvider);
//		setLabelProvider(labelProvider);
	}
	
	public void setParameters(TemplateParameterSet params) {
		fParameters = new TemplateParameterSet();
		if (params != null) {
			ITemplateParameterProvider pp = 
					SvtUiPlugin.getDefault().getGlobalTemplateParameters();
			
			for (TemplateParameterBase p : params.getParameters()) {
				TemplateParameterBase p_d = p.clone();
			
				// Change default value if global provides one
				if (pp.providesParameter(p.getName())) {
					if (p_d instanceof TemplateParameter) {
						((TemplateParameter)p_d).setValue(
								pp.getParameterValue(p.getName(), null));
					}
				}
		
				fParameters.addParameter(p_d);
			}
		}
		
		setInput(fParameters);
	}
	
	public TemplateParameterSet getParameters() {
		return fParameters;
	}
	
	public void addModifyListener(ModifyListener l) {
		fModifyListeners.add(l);
	}
	
	private void triggerListeners() {
		Event ev = new Event();
		ev.widget = getTree();
		ModifyEvent e = new ModifyEvent(ev);
		e.widget = this.getTree();
		for (ModifyListener l : fModifyListeners) {
			l.modifyText(e);
		}
	}

	IStructuredContentProvider contentProvider = new ITreeContentProvider() {
		
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }
		
		public void dispose() { }
		
		public boolean hasChildren(Object element) {
			if (element instanceof TemplateParameterBase) {
				TemplateParameterBase tp = (TemplateParameterBase)element;
				return (tp.getType() == TemplateParameterType.ParameterType_Composite ||
						tp.getType() == TemplateParameterType.ParameterType_Group);
			}
			return false;
		}
		
		public Object getParent(Object element) {
			// TODO Auto-generated method stub
			return null;
		}
		
		public Object[] getElements(Object inputElement) {
			/*
			List<TemplateParameterBase> visible_params = new ArrayList<TemplateParameterBase>();

			for (TemplateParameterBase p : fParameters.getParameters()) {
				if (p.getType() == TemplateParameterType.ParameterType_Group) {
					TemplateParameterGroup g = (TemplateParameterGroup)p;
					if (!g.isHidden()) {
						visible_params.add(g);
					}
				} else {
					visible_params.add(p);
				}
			}
			
			return visible_params.toArray();
			 */
			return fParameters.getParameters().toArray();
		}
		
		public Object[] getChildren(Object parentElement) {
			if (parentElement instanceof TemplateParameterBase) {
				TemplateParameterBase tp = (TemplateParameterBase)parentElement;
				if (tp.getType() == TemplateParameterType.ParameterType_Composite) {
					return ((TemplateParameterComposite)tp).getParameters().toArray();
				} else if (tp.getType() == TemplateParameterType.ParameterType_Group) {
					return ((TemplateParameterGroup)tp).getParameters().toArray();
				}
			}
			return new Object[0];
		}
	};

	ViewerFilter		hiddenItemsFilter = new ViewerFilter() {
		
		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			if (element instanceof TemplateParameterGroup) {
				TemplateParameterGroup g = (TemplateParameterGroup)element;
				return !g.isHidden();
			} else {
				return true;
			}
		}
	};

	private ColumnLabelProvider			nameLabelProvider = new ColumnLabelProvider() {

		@Override
		public String getText(Object element) {
			if (element instanceof TemplateParameterBase) {
				return ((TemplateParameterBase)element).getName();
			} else {
				return super.getText(element);
			}
		}
	};
	
	private ColumnLabelProvider			typeLabelProvider = new ColumnLabelProvider() {

		@Override
		public String getText(Object element) {
			if (element instanceof TemplateParameterBase) {
				switch (((TemplateParameterBase)element).getType()) {
					case ParameterType_Id: return "Id";
					case ParameterType_Int: return "Int";
					case ParameterType_Enum: return "Enum";
					case ParameterType_Class: return "Class";
					case ParameterType_Group: return "Group";
					case ParameterType_Composite: {
						return ((TemplateParameterComposite)element).getDefinitionType();
					}
					default: return ((TemplateParameterBase)element).getType().toString();
				}
			} else {
				return super.getText(element);
			}
		}
	};
	
	private ColumnLabelProvider			valueLabelProvider = new ColumnLabelProvider() {

		@Override
		public String getText(Object element) {
			if (element instanceof TemplateParameterBase) {
				TemplateParameterBase p = (TemplateParameterBase)element;
				
				if (p.getType() == TemplateParameterType.ParameterType_Composite ||
						p.getType() == TemplateParameterType.ParameterType_Group) {
					// These types don't really have values, since they're containers
					return "---";
				} else if (p instanceof TemplateParameter) {
					// Scalar template
					return ((TemplateParameter)p).getValue();
				} else {
					return "UNKNOWN " + p.getType();
				}
			} else {
				return super.getText(element);
			}
		}
	};
	
	private class ValueEditingSupport extends EditingSupport {
		
		public ValueEditingSupport(ColumnViewer viewer) {
			super(viewer);
		}

		@Override
		protected CellEditor getCellEditor(Object element) {
			if (element instanceof TemplateParameter) {
				TemplateParameter p = (TemplateParameter)element;
				
				switch (p.getType()) {
					case ParameterType_Enum: {
						fComboBoxCellEditor.setItems(p.getValues().toArray(
										new String[p.getValues().size()]));
						return fComboBoxCellEditor;
					}
			
					// TODO: implement more-appropriate editor for class-type parameter
					case ParameterType_Class:
					case ParameterType_Id: {
						return fTextCellEditor;
					}
					
					case ParameterType_Int: {
						return fIntCellEditor;
					}
					
					default:
						System.out.println("No editor supplied for " + p.getType());
						break;
				}
				
			}

			return null;
		}

		@Override
		protected boolean canEdit(Object element) {
			if (element instanceof TemplateParameterBase) {
				TemplateParameterBase p = (TemplateParameterBase)element;
				return (p.getType() == TemplateParameterType.ParameterType_Class ||
						p.getType() == TemplateParameterType.ParameterType_Enum ||
						p.getType() == TemplateParameterType.ParameterType_Id ||
						p.getType() == TemplateParameterType.ParameterType_Int);
			}
			return false;
		}

		@Override
		protected Object getValue(Object element) {
			if (element instanceof TemplateParameter) {
				TemplateParameter p = (TemplateParameter)element;
				
				switch (p.getType()) {
					case ParameterType_Enum: {
						int val_idx = p.getValues().indexOf(p.getValue());
						
						if (val_idx == -1) {
							val_idx = 0;
						}
				
						return new Integer(val_idx);
					}

					// TODO: provide a specific editor for class-type parameters
					case ParameterType_Class:
					case ParameterType_Id: {
						return p.getValue();
					}

					case ParameterType_Int: {
						return p.getValue();
					}
					
					default: return null;
				}
			}
			return null;
		}

		@Override
		protected void setValue(Object element, Object value) {
			if (element instanceof TemplateParameter) {
				TemplateParameter p = (TemplateParameter)element;
				
				switch (p.getType()) {
					case ParameterType_Enum: {
						int val_idx = (Integer)value;
						p.setValue(p.getValues().get(val_idx));
					} break;
				
					// TODO: provide specific implementation for class
					case ParameterType_Class:
					case ParameterType_Int:
					case ParameterType_Id:
						p.setValue((String)value);
						break;
						
					default:
						break;
				}
			}
			
			refresh();
			triggerListeners();
		}
	}
}
