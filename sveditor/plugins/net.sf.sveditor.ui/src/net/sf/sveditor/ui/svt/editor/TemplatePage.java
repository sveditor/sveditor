package net.sf.sveditor.ui.svt.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StackLayout;
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
	private Text						fFilePath;
	private Button						fFilePathBrowse;
	
	private Composite					fCategoryDetailsPane;
	private Text						fCategoryId;
	private Text						fCategoryName;
	
	public TemplatePage(SVTEditor editor) {
		super(editor, "id", "Template Definitions");
	}

	@Override
	protected void createFormContent(IManagedForm managedForm) {
		FormToolkit tk = managedForm.getToolkit();
		ScrolledForm form = managedForm.getForm();
		form.setText("Template");
		
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
		
		tk.createLabel(c, "Id:");
		fTemplateId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fTemplateId.setLayoutData(gd);
		
		tk.createLabel(c, "Category:");
		fTemplateCategoryId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fTemplateCategoryId.setLayoutData(gd);
		fTemplateCategoryBrowse = tk.createButton(c, "Browse...", SWT.PUSH);
		fTemplateCategoryBrowse.addSelectionListener(selectionListener);
		
		Group g = new Group(c, SWT.NONE);
		g.setText("Description");
		tk.adapt(g);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fTemplateDescription = tk.createText(g, "", SWT.BORDER+SWT.MULTI);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fTemplateDescription.setLayoutData(gd);
		
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
		
		tk.createLabel(c, "Type:");
		fParameterType = new Combo(c, SWT.READ_ONLY);
		fParameterType.setItems(new String[] {"id", "int", "class"});
		tk.adapt(fParameterType);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterType.setLayoutData(gd);
		
		tk.createLabel(c, "Restrictions:");
		fParameterRestrictions = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterRestrictions.setLayoutData(gd);
		
		tk.createLabel(c, "Class Extends From:");
		fParameterExtFromClass = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fParameterExtFromClass.setLayoutData(gd);
		
		fParameterExtFromClassBrowse = tk.createButton(c, "Browse...", SWT.PUSH);
		fParameterExtFromClassBrowse.addSelectionListener(selectionListener);
		
		tk.createLabel(c, "Default:");
		fParameterDefault = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fParameterDefault.setLayoutData(gd);
		
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
		
		tk.createLabel(c, "Path:");
		fFilePath = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fFilePath.setLayoutData(gd);
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
		
		tk.createLabel(c, "Name:");
		fCategoryName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fCategoryName.setLayoutData(gd);
		
		return c;
	}
	
	private void setTemplateContext(Element template) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);
		
		// 
		fActiveElement = template;
		
		fTemplateName.setText(getAttribute(template, "name"));
		fTemplateId.setText(getAttribute(template, "id"));
		fTemplateCategoryId.setText(getAttribute(template, "category"));
		
		fTemplateDescription.setText(getElementText(template, "description"));
		
		setDetailsPane(fTemplateDetailsPane);
	}
	
	private void setFileContext(Element file) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);

		fActiveElement = file;

		setDetailsPane(fFileDetailsPane);
	}

	private void setParameterContext(Element file) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);

		fActiveElement = file;

		setDetailsPane(fParameterDetailsPane);
	}

	private void setCategoryContext(Element category) {
		fAddButton.setEnabled(true);
		fRemoveButton.setEnabled(true);

		fActiveElement = category;

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
		// TODO Auto-generated method stub
		super.doSave(monitor);
	}
	
	private Element createTemplate() {
		Element ret = fDocument.createElement("template");
		Element doc = fDocument.createElement("description");
		ret.appendChild(doc);
		
		ret.setAttribute("name", "New Template");
		ret.setAttribute("id", "template.id");
		ret.setAttribute("category", "category.id");
		
		return ret;
	}
	
	private Element createCategory() {
		Element ret = fDocument.createElement("category");
		Element doc = fDocument.createElement("description");
		ret.appendChild(doc);

		ret.setAttribute("category", "category.id");

		return ret;
	}
	
	private Element createParameter() {
		Element ret = fDocument.createElement("parameter");
		
		return ret;
	}

	private Element createFile() {
		Element ret = fDocument.createElement("file");
		
		return ret;
	}

	private SelectionListener selectionListener = new SelectionListener() {
		public void widgetDefaultSelected(SelectionEvent e) {}
		
		public void widgetSelected(SelectionEvent e) {
			if (e.widget == fAddButton) {
				Element new_elem = null;
				Element target = null;
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
					fTreeViewer.refresh();
					fTreeViewer.setSelection(new StructuredSelection(new_elem), true);
				}
			} else if (e.widget == fRemoveButton) {
				fActiveElement.getParentNode().removeChild(fActiveElement);
				fTreeViewer.refresh();
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
	
	private String getAttribute(Element elem, String attr) {
		String ret = elem.getAttribute(attr);
		
		if (ret == null) {
			ret = "";
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
