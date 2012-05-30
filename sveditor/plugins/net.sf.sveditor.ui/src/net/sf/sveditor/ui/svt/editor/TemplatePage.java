package net.sf.sveditor.ui.svt.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.ui.EditorInputUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormPage;
import org.eclipse.ui.forms.widgets.ExpandableComposite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.eclipse.ui.forms.widgets.Section;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class TemplatePage extends FormPage {
	
	private TreeViewer					fTreeViewer;
	private Document					fDocument;
	private Element						fRoot;
	private Button						fAddButton;
	private Button						fRemoveButton;
	
	private StackLayout					fStackLayout;
	private Composite					fDetailsPaneParent;
	private Element						fActiveElement;
	
	private Composite					fNoDetailsPane;
	private Composite					fTemplateDetailsPane;
	private Text						fTemplateName;
	private Text						fTemplateId;
	private Text						fTemplateCategoryId;
	private Button						fTemplateCategoryBrowse;
	private Text						fTemplateDescription;
	
	private Composite					fParameterDetailsPane;
	private Text						fParameterName;
	private Combo						fParameterType;
	private Text						fParameterRestrictions;
	private Text						fParameterExtFromClass;
	private Button						fParameterExtFromClassBrowse;
	private Text						fParameterDefault;
	
	private Composite					fFileDetailsPane;
	private Text						fFileName;
	private Text						fTemplatePath;
	private Button						fFilePathBrowse;
	
	private Composite					fCategoryDetailsPane;
	private Text						fCategoryId;
	private Text						fCategoryName;
	private Text						fCategoryDescription;

	private boolean					fControlModify;
	private boolean					fIsDirty;
	
	private Map<Object, String>			fAttrMap;
	private Map	<Object, String>		fElemMap;
	
	private static List<String>		fTypeNames;
	
	static {
		fTypeNames = new ArrayList<String>();
		fTypeNames.add("id");
		fTypeNames.add("int");
		fTypeNames.add("enum");
		fTypeNames.add("class");
	}
	
	public TemplatePage(SVTEditor editor) {
		super(editor, "id", "Template Definitions");
		
		fAttrMap = new HashMap<Object, String>();
		fElemMap = new HashMap<Object, String>();
	}

	@Override
	protected void createFormContent(IManagedForm managedForm) {
		FormToolkit tk = managedForm.getToolkit();
		ScrolledForm form = managedForm.getForm();
		form.setText("Template");
		
		managedForm.dirtyStateChanged();
		
		Composite pane = form.getBody();
		pane.setLayout(new GridLayout(1, false));
		
		SashForm sash = new SashForm(pane, SWT.HORIZONTAL);
		sash.setSashWidth(2);
		sash.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Section s = tk.createSection(sash, ExpandableComposite.TITLE_BAR);
		s.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		s.setText("All Templates and Categories");
		Composite left = tk.createComposite(s, SWT.NONE);
		left.setLayout(new GridLayout(2, false));
		left.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		s.setClient(left);
		
		fTreeViewer = new TreeViewer(left);
		fTreeViewer.getTree().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fTreeViewer.setContentProvider(new SVTContentProvider());
		fTreeViewer.setLabelProvider(new SVTLabelProvider());
		fTreeViewer.setInput(fDocument);
		fTreeViewer.addSelectionChangedListener(selectionChangedListener);
		
		Composite bb = tk.createComposite(left);
		bb.setLayout(new GridLayout());
		bb.setLayoutData(new GridData(SWT.FILL, SWT.FILL, false, true));
		fAddButton = tk.createButton(bb, "Add", SWT.PUSH);
		fAddButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fAddButton.addSelectionListener(selectionListener);
		fRemoveButton = tk.createButton(bb, "Remove", SWT.PUSH);
		fRemoveButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		fRemoveButton.addSelectionListener(selectionListener);
		
		s = tk.createSection(sash, ExpandableComposite.TITLE_BAR);
		s.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		s.setText("Template/Category Details");
		fDetailsPaneParent = tk.createComposite(s, SWT.NONE);
		fStackLayout = new StackLayout();
		fDetailsPaneParent.setLayout(fStackLayout);
		fDetailsPaneParent.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		s.setClient(fDetailsPaneParent);
		
		// Create the various detail panes
		fNoDetailsPane = tk.createComposite(fDetailsPaneParent, SWT.NONE);
		
		fTemplateDetailsPane = createTemplateDetailsPane(tk, fDetailsPaneParent);
		
		fParameterDetailsPane = createParameterDetailsPane(tk, fDetailsPaneParent);
		
		fFileDetailsPane = createFileDetailsPane(tk, fDetailsPaneParent);
		
		fCategoryDetailsPane = createCategoryDetailsPane(tk, fDetailsPaneParent);

		fTreeViewer.setSelection(new StructuredSelection("Templates"));
		
		setDetailsPane(fNoDetailsPane);
	}
	
	private void setDetailsPane(Composite p) {
		fStackLayout.topControl = p;
		fDetailsPaneParent.layout();
	}
	
	private Composite createTemplateDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));
		
		tk.createLabel(c, "Name:");
		fTemplateName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fTemplateName.setLayoutData(gd);
		fTemplateName.addModifyListener(modifyListener);
		fAttrMap.put(fTemplateName, "name");
		
		tk.createLabel(c, "Id:");
		fTemplateId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fTemplateId.setLayoutData(gd);
		fTemplateId.addModifyListener(modifyListener);
		fAttrMap.put(fTemplateId, "name");
		
		tk.createLabel(c, "Category:");
		fTemplateCategoryId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		// TODO:
		gd.horizontalSpan = 2;
		fTemplateCategoryId.setLayoutData(gd);
		fTemplateCategoryId.addModifyListener(modifyListener);
		fAttrMap.put(fTemplateCategoryId, "category");
		/** TODO:
		fTemplateCategoryBrowse = tk.createButton(c, "Browse...", SWT.PUSH);
		fTemplateCategoryBrowse.addSelectionListener(selectionListener);
		 */
		
		Group g = new Group(c, SWT.NONE);
		g.setText("Description");
		tk.adapt(g);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fTemplateDescription = tk.createText(g, "", SWT.BORDER+SWT.MULTI+SWT.WRAP);
		fTemplateDescription.addModifyListener(modifyListener);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fTemplateDescription.setLayoutData(gd);
		fElemMap.put(fTemplateDescription, "description");
		
		return c;
	}

	private Composite createParameterDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));
		
		tk.createLabel(c, "Name:");
		fParameterName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterName.setLayoutData(gd);
		fParameterName.addModifyListener(modifyListener);
		fAttrMap.put(fParameterName, "name");
		
		tk.createLabel(c, "Type:");
		fParameterType = new Combo(c, SWT.READ_ONLY);
		fParameterType.setItems(fTypeNames.toArray(new String[fTypeNames.size()]));
		tk.adapt(fParameterType);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterType.setLayoutData(gd);
		fParameterType.addSelectionListener(selectionListener);
		
		tk.createLabel(c, "Restrictions:");
		fParameterRestrictions = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterRestrictions.setLayoutData(gd);
		fParameterRestrictions.addModifyListener(modifyListener);
		fAttrMap.put(fParameterRestrictions, "restrictions");
		
		tk.createLabel(c, "Class Extends From:");
		fParameterExtFromClass = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterExtFromClass.setLayoutData(gd);
		fParameterExtFromClass.addModifyListener(modifyListener);
		fAttrMap.put(fParameterExtFromClass, "extends_from");
		
		/** TODO:
		fParameterExtFromClassBrowse = tk.createButton(c, "Browse...", SWT.PUSH);
		fParameterExtFromClassBrowse.addSelectionListener(selectionListener);
		 */
		
		tk.createLabel(c, "Default:");
		fParameterDefault = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fParameterDefault.setLayoutData(gd);
		fParameterDefault.addModifyListener(modifyListener);
		fAttrMap.put(fParameterDefault, "default");
		
		return c;
	}

	private Composite createFileDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));

		tk.createLabel(c, "Name:");
		fFileName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fFileName.setLayoutData(gd);
		fFileName.addModifyListener(modifyListener);
		fAttrMap.put(fFileName, "name");
		
		tk.createLabel(c, "Template Path:");
		fTemplatePath = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fTemplatePath.setLayoutData(gd);
		fTemplatePath.addModifyListener(modifyListener);
		fAttrMap.put(fTemplatePath, "template");
		fFilePathBrowse = tk.createButton(c, "Browse...", SWT.PUSH);
		fFilePathBrowse.addSelectionListener(selectionListener);

		return c;
	}
	
	private Composite createCategoryDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(2, false));

		tk.createLabel(c, "Id:");
		fCategoryId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fCategoryId.setLayoutData(gd);
		fCategoryId.addModifyListener(modifyListener);
		fAttrMap.put(fCategoryId, "id");
		
		tk.createLabel(c, "Name:");
		fCategoryName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fCategoryName.setLayoutData(gd);
		fCategoryName.addModifyListener(modifyListener);
		fAttrMap.put(fCategoryName, "name");
		
		Group g = new Group(c, SWT.NONE);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 2;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		g.setText("Description");
		fCategoryDescription = tk.createText(g, "", SWT.BORDER+SWT.MULTI+SWT.WRAP);
		fCategoryDescription.addModifyListener(modifyListener);
		fElemMap.put(fCategoryDescription, "description");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fCategoryDescription.setLayoutData(gd);
		
		return c;
	}
	
	private void setTemplateContext(Element template) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);
		
		// 
		fActiveElement = template;
		
		fControlModify = true;
		
		fTemplateName.setText(getAttribute(template, "name"));
		fTemplateId.setText(getAttribute(template, "id"));
		fTemplateCategoryId.setText(getAttribute(template, "category"));
		
		fTemplateDescription.setText(getElementText(template, "description"));

		fControlModify = false;

		setDetailsPane(fTemplateDetailsPane);
	}
	
	private void setFileContext(Element file) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);

		fActiveElement = file;
		
		fControlModify = true;
		
		fFileName.setText(getAttribute(fActiveElement, "name"));
		fTemplatePath.setText(getAttribute(fActiveElement, "template"));

		fControlModify = false;
		setDetailsPane(fFileDetailsPane);
	}

	private void setParameterContext(Element file) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);

		fActiveElement = file;
		
		fControlModify = true;
		
		fParameterName.setText(getAttribute(fActiveElement, "name"));
		fParameterType.select(getTypeIndex(getAttribute(fActiveElement, "type")));
		fParameterDefault.setText(getAttribute(fActiveElement, "default"));
		fParameterExtFromClass.setText(getAttribute(fActiveElement, "extends_from"));
		fParameterRestrictions.setText(getAttribute(fActiveElement, "restrictions"));
		
		updateParameterFields();
		
		fControlModify = false;

		setDetailsPane(fParameterDetailsPane);
	}
	
	private void updateParameterFields() {
		String type = fParameterType.getText();
		
		fControlModify = true;
		
		if (type.equals("id") || type.equals("int")) {
			fParameterExtFromClass.setText("");
			fParameterExtFromClass.setEnabled(false);
			fParameterRestrictions.setText("");
			fParameterRestrictions.setEnabled(false);
		} else if (type.equals("enum")) {
			fParameterExtFromClass.setText("");
			fParameterExtFromClass.setEnabled(false);
			fParameterRestrictions.setText(getAttribute(fActiveElement, "restrictions"));
			fParameterRestrictions.setEnabled(true);
		} else if (type.equals("class")) {
			fParameterExtFromClass.setText(getAttribute(fActiveElement, "extends_from"));
			fParameterExtFromClass.setEnabled(true);
			fParameterRestrictions.setText("");
			fParameterRestrictions.setEnabled(false);
		} else {
			// ??
		}
		
		fControlModify = false;
	}

	private void setCategoryContext(Element category) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);

		fActiveElement = category;
		
		fControlModify = true;
		
		fCategoryId.setText(getAttribute(fActiveElement, "id"));
		fCategoryName.setText(getAttribute(fActiveElement, "name"));
		fCategoryDescription.setText(getElementText(fActiveElement, "description"));
		
		fControlModify = false;

		setDetailsPane(fCategoryDetailsPane);
	}

	public void setRoot(Document doc, Element root) {
		fRoot 		= root;
		fDocument 	= doc;
		if (fTreeViewer != null && !fTreeViewer.getTree().isDisposed()) {
			fTreeViewer.setInput(fDocument);
		}
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		fIsDirty = false;
		getEditor().editorDirtyStateChanged();
	}
	
	@Override
	public boolean isDirty() {
		return fIsDirty;
	}

	private Element createTemplate() {
		Element ret = fDocument.createElement("template");
		Element doc = fDocument.createElement("description");
		ret.appendChild(doc);
		
		ret.setAttribute("name", "New Template");
		ret.setAttribute("id", "template.id");
		ret.setAttribute("category", "category.id");
		
		Element parameters = fDocument.createElement("parameters");
		ret.appendChild(parameters);
		Element files = fDocument.createElement("files");
		ret.appendChild(files);
		
		return ret;
	}
	
	private Element createCategory() {
		Element ret = fDocument.createElement("category");
		Element doc = fDocument.createElement("description");
		ret.appendChild(doc);

		ret.setAttribute("category", "category.id");
		ret.setAttribute("name", "New Category");

		return ret;
	}
	
	private Element createParameter() {
		Element ret = fDocument.createElement("parameter");
		
		ret.setAttribute("type", "id");
		ret.setAttribute("name", "");
		ret.setAttribute("default", "");
		
		return ret;
	}

	private Element createFile() {
		Element ret = fDocument.createElement("file");
		
		return ret;
	}
	
	private void addElement() {
		Element new_elem = null;
		Element target = null;
		
		System.out.println("Active Element: " + fActiveElement.getNodeName());
		if (fActiveElement.getNodeName().equals("Templates") ||
				fActiveElement.getNodeName().equals("template")) {
			// Create a new template
			if (fActiveElement.getNodeName().equals("Templates")) {
				target = fRoot;
			} else {
				target = (Element)fActiveElement.getParentNode();
			}
			new_elem = createTemplate();
		} else if (fActiveElement.getNodeName().equals("Categories") ||
				fActiveElement.getNodeName().equals("category")) {
			if (fActiveElement.getNodeName().equals("Categories")) {
				target = fRoot;
			} else {
				target = (Element)fActiveElement.getParentNode();
			}
			new_elem = createCategory();
		} else if (fActiveElement.getNodeName().equals("parameters") ||
				fActiveElement.getNodeName().equals("parameter")) {
			if (fActiveElement.getNodeName().equals("parameters")) {
				target = fActiveElement;
			} else {
				target = (Element)fActiveElement.getParentNode();
			}
			new_elem = createParameter();
		} else if (fActiveElement.getNodeName().equals("files") ||
				fActiveElement.getNodeName().equals("file")) {
			if (fActiveElement.getNodeName().equals("files")) {
				target = fActiveElement;
			} else {
				target = (Element)fActiveElement.getParentNode();
			}
			new_elem = createFile();
		}
		
		if (new_elem != null) {
			target.appendChild(new_elem);
			fActiveElement = new_elem;
			fTreeViewer.refresh();
			fTreeViewer.getTree().getDisplay().asyncExec(new Runnable() {
				public void run() {
					fTreeViewer.expandToLevel(fActiveElement, 0);
					fTreeViewer.setSelection(new StructuredSelection(fActiveElement), true);
				}
			});
			// TODO: notify dirty
			fIsDirty = true;
			getEditor().editorDirtyStateChanged();
		}
	}
	
	private void removeElement() {
		fActiveElement.getParentNode().removeChild(fActiveElement);
		fTreeViewer.refresh();
		
		fIsDirty = true;
		getEditor().editorDirtyStateChanged();
	}

	private SelectionListener selectionListener = new SelectionListener() {
		public void widgetDefaultSelected(SelectionEvent e) {}
		
		public void widgetSelected(SelectionEvent e) {
			if (e.widget == fAddButton) {
				addElement();
			} else if (e.widget == fRemoveButton) {
				removeElement();
			} else if (e.widget == fParameterType) {
				if (!fControlModify) {
					setAttr(fActiveElement, "type", fParameterType.getText());
					updateParameterFields();
					fIsDirty = true;
					getEditor().editorDirtyStateChanged();
				}
			} else if (e.widget == fFilePathBrowse) {
				Tuple<File, IFile> ret = EditorInputUtils.getFileLocation(getEditorInput());
				
				FileBrowseDialog dlg;
				
				if (ret.first() != null) {
					dlg = new FileBrowseDialog(fDetailsPaneParent.getShell(), 
							ret.first().getParentFile());
				} else {
					dlg = new FileBrowseDialog(fDetailsPaneParent.getShell(), 
							ret.second().getParent());
				}
				
				if (dlg.open() == Window.OK) {
					fTemplatePath.setText(dlg.getSelectedFile());
				}
			}
		}
	};

	private ISelectionChangedListener selectionChangedListener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection ss = (IStructuredSelection)event.getSelection();
			
			if (ss.getFirstElement() == null) {
			} else if (ss.getFirstElement() instanceof String) {
				String e = (String)ss.getFirstElement();
				
				fAddButton.setEnabled(true);
				fRemoveButton.setEnabled(false);
				setDetailsPane(fNoDetailsPane);
				
				fActiveElement = fDocument.createElement(e);
			} else {
				Element e = (Element)ss.getFirstElement();
				fActiveElement = e;
				if (e.getNodeName().equals("sv_template") ||
						e.getNodeName().equals("parameters") ||
						e.getNodeName().equals("files")) {
					fAddButton.setEnabled(true);
					fRemoveButton.setEnabled(false);
					setDetailsPane(fNoDetailsPane);
				} else if (e.getNodeName().equals("template")) {
					setTemplateContext(e);
				} else if (e.getNodeName().equals("file")) {
					setFileContext(e);
				} else if (e.getNodeName().equals("parameter")) {
					setParameterContext(e);
				} else if (e.getNodeName().equals("category")) {
					setCategoryContext(e);
				} else {
					// ??
				}
			}
		}
	};
	
	private ModifyListener modifyListener = new ModifyListener() {
		
		public void modifyText(ModifyEvent e) {
			if (fControlModify) {
				return;
			}
			
			if (fAttrMap.containsKey(e.widget)) {
				setAttr(fActiveElement, fAttrMap.get(e.widget), 
						((Text)e.widget).getText());
			} else if (fElemMap.containsKey(e.widget)) {
				setElem(fActiveElement, fElemMap.get(e.widget), 
						((Text)e.widget).getText());
			}

			fIsDirty = true;
			getEditor().editorDirtyStateChanged();
			fTreeViewer.refresh();
		}
	};
	
	private void setAttr(Element elem, String attr, String value) {
		elem.setAttribute(attr, value);
	}

	private void setElem(Element elem, String e_name, String value) {
		NodeList nl = elem.getElementsByTagName(e_name);
		Element e;
		
		if (nl.getLength() > 0) {
			e = (Element)nl.item(0);
		} else {
			e = fDocument.createElement(e_name);
			elem.appendChild(e);
		}
		e.setTextContent(value);
	}
	
	private int getTypeIndex(String type) {
		int ret = fTypeNames.indexOf(type);
		
		if (ret == -1) {
			ret = 0;
		}
		
		return ret; 
	}

	private String getAttribute(Element elem, String attr) {
		return getAttribute(elem, attr, "");
	}

	private String getAttribute(Element elem, String attr, String dflt) {
		String ret = elem.getAttribute(attr);
		
		if (ret == null) {
			ret = dflt;
		}
		
		return ret;
	}

	private String getElementText(Element elem, String c_elem) {
		NodeList nl = elem.getElementsByTagName(c_elem);
		String ret = "";
		
		if (nl.getLength() != 0) {
			ret = nl.item(0).getTextContent();
		}
		
		return ret;
	}
	
}
