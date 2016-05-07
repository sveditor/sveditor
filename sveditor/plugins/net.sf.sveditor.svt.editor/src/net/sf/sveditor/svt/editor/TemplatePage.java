package net.sf.sveditor.svt.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.ui.EditorInputUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerDropAdapter;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.dnd.DND;
import org.eclipse.swt.dnd.DragSourceEvent;
import org.eclipse.swt.dnd.DragSourceListener;
import org.eclipse.swt.dnd.DropTargetEvent;
import org.eclipse.swt.dnd.TextTransfer;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.dnd.TransferData;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.swt.events.VerifyListener;
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
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class TemplatePage extends FormPage {
	
	private TreeViewer					fTreeViewer;
	private Document					fDocument;
	private Element						fRoot;
	
	private StackLayout					fButtonLayout;
	private Composite					fButtonPaneParent;
	
	private Composite					fParameterButtons;
	private Button						fAddParameterButton;
	private Button						fAddParameterGroupButton;
	private Button						fRemoveParameterButton;
	private Button						fMoveParameterUpButton;
	private Button						fMoveParameterDownButton;

	/*
	private Composite					fFilesButtons;
	private Button						fAddFileButton;
	private Button						fAddFilesButton;
	 */
	
	private Composite					fDefaultButtons;
	private Button						fAddButton;
	private Button						fRemoveButton;
	private Button						fUpButton;
	private Button						fDownButton;
	
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
	private Text						fParameterDescription;
	
	private Composite					fParameterGroupDetailsPane;
	private Text						fParameterGroupName;
	private Button						fParameterGroupHidden;
	private Text						fParameterGroupDescription;
	
	private Composite					fFileDetailsPane;
	private Text						fFileName;
	private Text						fTemplatePath;
	private Button						fFilePathBrowse;
	private Button						fFileIsExecutable;
	
	private Composite					fCategoryDetailsPane;
	private Text						fCategoryId;
	private Text						fCategoryName;
	private Text						fCategoryDescription;

	private boolean						fControlModify;
	private boolean						fIsDirty;
	private boolean						fIsReadOnly = false;
	
	private Map<Object, String>			fAttrMap;
	private Map	<Object, String>		fElemMap;
	private SVTEditor					fSvtEditor;
	
	private List<Text>					fTextFields;
	private List<Button>				fButtons;
	
	private static List<String>			fTypeNames;
	
	static {
		fTypeNames = new ArrayList<String>();
		fTypeNames.add("id");
		fTypeNames.add("int");
		fTypeNames.add("enum");
		fTypeNames.add("class");
	}
	
	public TemplatePage(SVTEditor editor) {
		super(editor, "id", "Template Definitions");
		
		fSvtEditor = editor;
		
		fAttrMap = new HashMap<Object, String>();
		fElemMap = new HashMap<Object, String>();
		
		fTextFields = new ArrayList<Text>();
		fButtons = new ArrayList<Button>();
	}
	
	public void setReadOnlyState(boolean ro) {
		fIsReadOnly = ro;
		
		for (Button b : fButtons) {
			b.setEnabled(!ro);
		}
		for (Text t : fTextFields) {
			t.setEnabled(!ro);
		}
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
		int operations = DND.DROP_MOVE;
		Transfer transfer_types[] = new Transfer[] {TextTransfer.getInstance()};
		
		fTreeViewer.addDragSupport(operations, transfer_types, 
				new TemplateDragSource(fTreeViewer));
		fTreeViewer.addDropSupport(operations, transfer_types,
				new TemplateDropAdapter(fTreeViewer));
	
		fTreeViewer.getTree().addKeyListener(keyListener);
		fTreeViewer.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				boolean exp = fTreeViewer.getExpandedState(sel.getFirstElement());
				fTreeViewer.setExpandedState(sel.getFirstElement(), !exp);
			}
		});
		
		fButtonPaneParent = tk.createComposite(left);
		fButtonLayout = new StackLayout();
		fButtonPaneParent.setLayout(fButtonLayout);
		fButtonPaneParent.setLayoutData(new GridData(SWT.FILL, SWT.FILL, false, true));
		
		createButtons(tk, fButtonPaneParent);
		
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
		
		fParameterGroupDetailsPane = createParameterGroupDetailsPane(tk, fDetailsPaneParent);
		
		fFileDetailsPane = createFileDetailsPane(tk, fDetailsPaneParent);
		
		fCategoryDetailsPane = createCategoryDetailsPane(tk, fDetailsPaneParent);

		fTreeViewer.setSelection(new StructuredSelection("Templates"));
		
		setDetailsPane(fNoDetailsPane);
		setButtonsPane(fDefaultButtons);
	}
	
	private void createButtons(FormToolkit tk, Composite bb) {
		// Create the Parameter buttons
		fParameterButtons = tk.createComposite(bb);
		fParameterButtons.setLayout(new GridLayout());
		
		fAddParameterButton = tk.createButton(fParameterButtons, "Add Para&meter", SWT.PUSH);
		fAddParameterButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fAddParameterButton);
		fAddParameterGroupButton = tk.createButton(fParameterButtons, "Add &Group", SWT.PUSH);
		fAddParameterGroupButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fAddParameterGroupButton);
		fRemoveParameterButton = tk.createButton(fParameterButtons, "R&emove", SWT.PUSH);
		fRemoveParameterButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fRemoveParameterButton);
		fMoveParameterUpButton = tk.createButton(fParameterButtons, "&Up", SWT.PUSH);
		fMoveParameterUpButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fMoveParameterUpButton);
		fMoveParameterDownButton = tk.createButton(fParameterButtons, "D&own", SWT.PUSH);
		fMoveParameterDownButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fMoveParameterDownButton);
		
		// Create the default buttons
		fDefaultButtons = tk.createComposite(bb);
		fDefaultButtons.setLayout(new GridLayout());
		fAddButton = tk.createButton(fDefaultButtons, "A&dd", SWT.PUSH);
		fAddButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fAddButton);
		fRemoveButton = tk.createButton(fDefaultButtons, "Remo&ve", SWT.PUSH);
		fRemoveButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fRemoveButton);
		
		fUpButton = tk.createButton(fDefaultButtons, "&Up", SWT.PUSH);
		fUpButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fUpButton);
		
		fDownButton = tk.createButton(fDefaultButtons, "D&own", SWT.PUSH);
		fDownButton.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		initButton(fDownButton);
		
	}
	
	private void initButton(Button button) {
		button.addSelectionListener(selectionListener);
		fButtons.add(button);
	}
	
	private void setDetailsPane(Composite p) {
		fStackLayout.topControl = p;
		fDetailsPaneParent.layout();
	}
	
	private void setButtonsPane(Composite p) {
		fButtonLayout.topControl = p;
		fButtonPaneParent.layout();
	}
	
	private Composite createTemplateDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));
		
		tk.createLabel(c, "Na&me:");
		fTemplateName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fTemplateName.setLayoutData(gd);
		addTextListeners(fTemplateName, "name");
		
		tk.createLabel(c, "&Id:");
		fTemplateId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fTemplateId.setLayoutData(gd);
		addTextListeners(fTemplateId, "id");
		
		tk.createLabel(c, "&Category:");
		fTemplateCategoryId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		// TODO:
		gd.horizontalSpan = 2;
		fTemplateCategoryId.setLayoutData(gd);
		addTextListeners(fTemplateCategoryId, "category");
		/** TODO:
		fTemplateCategoryBrowse = tk.createButton(c, "Browse...", SWT.PUSH);
		fTemplateCategoryBrowse.addSelectionListener(selectionListener);
		 */
		
		Group g = new Group(c, SWT.NONE);
		g.setText("Descrip&tion");
		tk.adapt(g);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fTemplateDescription = tk.createText(g, "", 
				SWT.BORDER+SWT.MULTI+SWT.WRAP+SWT.V_SCROLL);
		addTextListeners(fTemplateDescription, "description");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fTemplateDescription.setLayoutData(gd);
		
		return c;
	}
	
	private void addTextListeners(Text text, String id) {
		text.addModifyListener(modifyListener);
		text.addVerifyListener(verifyListener);
		
		fAttrMap.put(text, id);
		
		fTextFields.add(text);
	}

	private Composite createParameterDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));
		
		tk.createLabel(c, "Na&me:");
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
	
		/*
		tk.createLabel(c, "Class Extends From:");
		fParameterExtFromClass = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterExtFromClass.setLayoutData(gd);
		fParameterExtFromClass.addModifyListener(modifyListener);
		fAttrMap.put(fParameterExtFromClass, "extends_from");
		 */
		
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
		
		Group g = new Group(c, SWT.NONE);
		g.setText("Descrip&tion");
		tk.adapt(g);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fParameterDescription = tk.createText(g, "", 
				SWT.BORDER+SWT.MULTI+SWT.WRAP+SWT.V_SCROLL);
		fParameterDescription.addModifyListener(modifyListener);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fParameterDescription.setLayoutData(gd);
		fElemMap.put(fParameterDescription, "description");		
		
		return c;
	}

	private Composite createParameterGroupDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));
		
		tk.createLabel(c, "Na&me:");
		fParameterGroupName = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fParameterGroupName.setLayoutData(gd);
		fParameterGroupName.addModifyListener(modifyListener);
		fAttrMap.put(fParameterGroupName, "name");
		
		tk.createLabel(c, "Hidden:");
		fParameterGroupHidden = tk.createButton(c, "", SWT.CHECK);
		gd = new GridData(SWT.LEFT, SWT.CENTER, false, false);
		gd.horizontalSpan = 2;
		fParameterGroupHidden.setLayoutData(gd);
		fParameterGroupHidden.addSelectionListener(selectionListener);
		fAttrMap.put(fParameterGroupHidden, "hidden");
		
		Group g = new Group(c, SWT.NONE);
		g.setText("Descrip&tion");
		tk.adapt(g);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 3;
		g.setLayoutData(gd);
		g.setLayout(new GridLayout());
		fParameterGroupDescription = tk.createText(g, "", 
				SWT.BORDER+SWT.MULTI+SWT.WRAP+SWT.V_SCROLL);
		fParameterGroupDescription.addModifyListener(modifyListener);
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fParameterGroupDescription.setLayoutData(gd);
		fElemMap.put(fParameterGroupDescription, "description");		
		
		return c;
	}
	
	private Composite createFileDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(3, false));

		tk.createLabel(c, "Na&me:");
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
		
		tk.createLabel(c, "Executable:");
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.horizontalSpan = 2;
		fFileIsExecutable = tk.createButton(c, "", SWT.CHECK);
		fFileIsExecutable.setLayoutData(gd);
		fFileIsExecutable.addSelectionListener(selectionListener);
	
		fAttrMap.put(fFileIsExecutable, "executable");

		return c;
	}
	
	private Composite createCategoryDetailsPane(
			FormToolkit			tk,
			Composite 			parent) {
		GridData gd;
		Composite c = tk.createComposite(parent);
		c.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		c.setLayout(new GridLayout(2, false));

		tk.createLabel(c, "&Id:");
		fCategoryId = tk.createText(c, "", SWT.BORDER+SWT.SINGLE);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		fCategoryId.setLayoutData(gd);
		fCategoryId.addModifyListener(modifyListener);
		fAttrMap.put(fCategoryId, "id");
		
		tk.createLabel(c, "Na&me:");
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
		g.setText("Descrip&tion");
		fCategoryDescription = tk.createText(g, "", 
				SWT.BORDER+SWT.MULTI+SWT.WRAP+SWT.V_SCROLL);
		fCategoryDescription.addModifyListener(modifyListener);
		fElemMap.put(fCategoryDescription, "description");
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		fCategoryDescription.setLayoutData(gd);
		
		return c;
	}
	
	private void setTemplateContext(Element template) {
		fAddButton.setEnabled(!fIsReadOnly);
		fRemoveButton.setEnabled(!fIsReadOnly);
	
		updateUpDownButtonState();
		
		// 
		fActiveElement = template;
		
		fControlModify = true;
		
		fTemplateName.setText(getAttribute(template, "name"));
		fTemplateId.setText(getAttribute(template, "id"));
		fTemplateCategoryId.setText(getAttribute(template, "category"));
		
		fTemplateDescription.setText(getElementText(template, "description"));

		fControlModify = false;

		setDetailsPane(fTemplateDetailsPane);
		setButtonsPane(fDefaultButtons);
	}
	
	private void updateUpDownButtonState() {
		IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();

		boolean up_en   = !fIsReadOnly;
		boolean down_en = !fIsReadOnly;
		
		up_en &= (sel.size() == 1);
		down_en &= (sel.size() == 1);
		
		if (sel.size() == 1) {
			Element template = (Element)sel.getFirstElement();
			Node prev_sib = getPrevSiblingElement(template);
			Node next_sib = getNextSiblingElement(template);

			up_en   &= (prev_sib != null);
			down_en &= (next_sib != null);
		}
		
		fUpButton.setEnabled(up_en);
		fDownButton.setEnabled(down_en);
	}
	
	private int indexOf(NodeList node_list, Node node) {
		int ret = -1;
		Node n;
		
		for (int i=0; (n = node_list.item(i)) != null; i++) {
			if (n == node) {
				ret = i;
				break;
			}
		}
		
		return ret;
	}
	
	private int numElems(NodeList node_list) {
		int ret = 0;
		
		for (int i=0; node_list.item(i) != null; i++) {
			ret++;
		}
		
		return ret;
	}
	
	private void setFileContext(Element file) {
		fAddButton.setEnabled(!fIsReadOnly);
		fRemoveButton.setEnabled(!fIsReadOnly);

		fActiveElement = file;
		
		fControlModify = true;
		
		updateUpDownButtonState();
		
		fFileName.setText(getAttribute(fActiveElement, "name"));
		fTemplatePath.setText(getAttribute(fActiveElement, "template"));
		fFileIsExecutable.setSelection(getBooleanAttribute(fActiveElement, "executable", false));

		fControlModify = false;
		setDetailsPane(fFileDetailsPane);
		setButtonsPane(fDefaultButtons);
	}
	
	private void setParameterContext(Element parameter) {
		fAddButton.setEnabled(!fIsReadOnly);
		fRemoveButton.setEnabled(!fIsReadOnly);

		fActiveElement = parameter;
		
		fControlModify = true;
		
		updateParameterUpDownButtons();
		
		fParameterName.setText(getAttribute(fActiveElement, "name"));
		fParameterType.select(getTypeIndex(getAttribute(fActiveElement, "type")));
		fParameterDefault.setText(getAttribute(fActiveElement, "default"));
		/*
		fParameterExtFromClass.setText(getAttribute(fActiveElement, "extends_from"));
		 */
		fParameterRestrictions.setText(getAttribute(fActiveElement, "restrictions"));
		
		fParameterDescription.setText(getElementText(fActiveElement, "description"));
		
		updateParameterFields();
		
		fControlModify = false;

		setDetailsPane(fParameterDetailsPane);
		setButtonsPane(fParameterButtons);
	}
	
	private void updateParameterUpDownButtons() {
		IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
		boolean up_en = (sel.size() == 1);
		boolean down_en = (sel.size() == 1);
		
		if (sel.size() == 1) {
			Element el = (Element)sel.getFirstElement();
			Node next_n = getNextSiblingElement(el);
			Node prev_n = getPrevSiblingElement(el);
	
			up_en 	&= (prev_n != null);
			down_en &= (next_n != null);
		}
		
		fMoveParameterDownButton.setEnabled(down_en);
		fMoveParameterUpButton.setEnabled(up_en);
	}
	
	private void setParameterGroupContext(Element file) {
		fAddParameterButton.setEnabled(!fIsReadOnly);
		fAddParameterGroupButton.setEnabled(!fIsReadOnly);
		fRemoveParameterButton.setEnabled(!fIsReadOnly);
		// TODO: Up/Down

		fActiveElement = file;
		
		fControlModify = true;
	
		fParameterGroupName.setText(getAttribute(fActiveElement, "name"));
		fParameterGroupDescription.setText(getElementText(fActiveElement, "description"));
		fParameterGroupHidden.setSelection(getBooleanAttribute(fActiveElement, "hidden", false));
		
		fControlModify = false;

		setDetailsPane(fParameterGroupDetailsPane);
		setButtonsPane(fParameterButtons);
	}
	
	private void updateParameterFields() {
		String type = fParameterType.getText();
		
		fControlModify = true;
		
		if (type.equals("id") || type.equals("int")) {
			/*
			fParameterExtFromClass.setText("");
			fParameterExtFromClass.setEnabled(false);
			 */
			fParameterRestrictions.setText("");
			fParameterRestrictions.setEnabled(false);
		} else if (type.equals("enum")) {
			/*
			fParameterExtFromClass.setText("");
			fParameterExtFromClass.setEnabled(false);
			 */
			fParameterRestrictions.setText(getAttribute(fActiveElement, "restrictions"));
			fParameterRestrictions.setEnabled(true);
		} else if (type.equals("class")) {
			/*
			fParameterExtFromClass.setText(getAttribute(fActiveElement, "extends_from"));
			fParameterExtFromClass.setEnabled(true);
			 */
			fParameterRestrictions.setText("");
			fParameterRestrictions.setEnabled(false);
		} else {
			// ??
		}
		
		fControlModify = false;
	}

	private void setCategoryContext(Element category) {
		fAddButton.setEnabled(!fIsReadOnly);
		fRemoveButton.setEnabled(!fIsReadOnly);

		fActiveElement = category;
		
		fControlModify = true;
		
		fCategoryId.setText(getAttribute(fActiveElement, "id"));
		fCategoryName.setText(getAttribute(fActiveElement, "name"));
		fCategoryDescription.setText(getElementText(fActiveElement, "description"));
		
		fControlModify = false;

		setDetailsPane(fCategoryDetailsPane);
		setButtonsPane(fDefaultButtons);
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

	private Element createParameterGroup() {
		Element ret = fDocument.createElement("group");
		
		ret.setAttribute("name", "");
		
		return ret;
	}
	
	private Element createFile() {
		Element ret = fDocument.createElement("file");
		
		ret.setAttribute("executable", "false");
		
		return ret;
	}
	
	private void addElement() {
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
			Tuple<File, IFile> ret = EditorInputUtils.getFileLocation(getEditorInput());
			if (fActiveElement.getNodeName().equals("files")) {
				target = fActiveElement;
			} else {
				target = (Element)fActiveElement.getParentNode();
			}
			
			FileBrowseDialog dlg;
			if (ret.first() != null) {
				dlg = new FileBrowseDialog(fAddButton.getShell(),
						ret.first().getParentFile(), SWT.MULTI);
			} else {
				dlg = new FileBrowseDialog(fAddButton.getShell(),
						ret.second().getParent(), SWT.MULTI);
			}
			
			if (dlg.open() == Window.OK) {
				List<String> paths_i = dlg.getSelectedFiles();
				List<String> paths = new ArrayList<String>();
				
				for (String path : paths_i) {
					if (!paths.contains(path)) {
						paths.add(path);
					}
				}
				
				Element first_elem = null;
				
				for (String path : paths) {
					Element elem = createFile();
					setAttr(elem, "template", path);
					String leaf = new File(path).getName();
					setAttr(elem, "name", leaf);
					
					target.appendChild(elem);
					
					if (first_elem == null) {
						first_elem = elem;
					}
				}
				fActiveElement = first_elem;
				fTreeViewer.refresh();
				fTreeViewer.getTree().getDisplay().asyncExec(new Runnable() {
					public void run() {
						fTreeViewer.expandToLevel(fActiveElement, 0);
						fTreeViewer.setSelection(new StructuredSelection(fActiveElement), true);
					}
				});

				fIsDirty = true;
				getEditor().editorDirtyStateChanged();
			}
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
		List<Node> elems = getSelectedNodes();
		
		for (Node n : elems) {
			Node p = n.getParentNode();
			p.removeChild(n);
		}
	
		// TODO: must set new selection
		
		fTreeViewer.refresh();
		
		fIsDirty = true;
		getEditor().editorDirtyStateChanged();
	}
	
	private void moveTemplateUp() {
		List<Node> sel_nodes = getSelectedNodes();

		if (sel_nodes.size() > 0) {
			Node prev_node = getPrevSiblingElement(sel_nodes.get(sel_nodes.size()-1));
			Node parent = sel_nodes.get(0).getParentNode();
			
			unlinkNodes(sel_nodes);
			
			if (prev_node == null) {
				insertNodesInside(parent, sel_nodes);
			} else {
				insertNodesBefore(prev_node, sel_nodes);
			}
			fIsDirty = true;
			fTreeViewer.refresh();
			getEditor().editorDirtyStateChanged();
			
			updateUpDownButtonState();
		}
	}
	
	private void moveTemplateDown() {
		List<Node> sel_nodes = getSelectedNodes();
	
		if (sel_nodes.size() > 0) {
			Node next_node = getNextSiblingElement(sel_nodes.get(sel_nodes.size()-1));
			Node parent = sel_nodes.get(0).getParentNode();
			
			unlinkNodes(sel_nodes);
			
			if (next_node == null) {
				insertNodesInside(parent, sel_nodes);
			} else {
				insertNodesAfter(next_node, sel_nodes);
			}
			
			fIsDirty = true;
			fTreeViewer.refresh();
			getEditor().editorDirtyStateChanged();
			
			updateUpDownButtonState();
		}
	}
	
	private void addParameter() {
		Element new_elem = null;
		Node next_elem = null;
		

		
		new_elem = createParameter();
		
		if (new_elem != null) {
			if (fActiveElement.getNodeName().equals("parameters")) {
				fActiveElement.appendChild(new_elem);
			} else {
				next_elem = fActiveElement;
				while ((next_elem = next_elem.getNextSibling()) != null && 
						!(next_elem instanceof Element)) { }
				fActiveElement.getParentNode().insertBefore(new_elem, next_elem);
			}
			
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
	
	private void addParameterGroup() {
		Element new_elem = null;
		Element target = null;
		Element next_elem = null;

		if (fActiveElement.getNodeName().equals("parameters")) {
			target = fActiveElement;
		} else {
			target = (Element)fActiveElement.getParentNode();
		}
		
//		next_elem = (Element)fActiveElement.getNextSibling();
		
		new_elem = createParameterGroup();
		
		insertElement(fActiveElement, "parameters", new_elem);
		fActiveElement = new_elem;
		fTreeViewer.refresh();
		fTreeViewer.getTree().getDisplay().asyncExec(new Runnable() {
			public void run() {
				fTreeViewer.expandToLevel(fActiveElement, 0);
				fTreeViewer.setSelection(new StructuredSelection(fActiveElement), true);
			}
		});		
		fIsDirty = true;
		getEditor().editorDirtyStateChanged();
	
		/*
		if (new_elem != null) {
			target.insertBefore(new_elem, next_elem);
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
		 */	
	}
	
	private void removeParameter() {
		// TODO: should probably recognize multiple selected parameters
		
		// Locate the new element to select
		Element new_selection = null;
		
		Element parent = (Element)fActiveElement.getParentNode();
		List<Element> el_l = getElements(parent.getChildNodes());
		
		for (int i=0; i<el_l.size(); i++) {
			Element n = el_l.get(i);

			if (fActiveElement == n) {
				if (i == 0 && (i+1) >= el_l.size()) {
					// Select the parent
					new_selection = fActiveElement;
				} else if (i+1 >= el_l.size()) {
					// End of the non-zero list
					new_selection = el_l.get(i-1);
				} else {
					// New selection is the next element
					new_selection = el_l.get(i+1);
				}
			}
		}

		fActiveElement.getParentNode().removeChild(fActiveElement);
		fTreeViewer.refresh();
		
		fIsDirty = true;
		getEditor().editorDirtyStateChanged();
		
		fTreeViewer.setSelection(new StructuredSelection(new_selection));
	}
	
	private void moveParameterUp() {
		List<Node> sel_nodes = getSelectedNodes();
		
		if (sel_nodes.size() > 0) {
			// TODO: need to detect when we have a heterogeneous selection
			Node prev_node = getPrevSiblingElement(sel_nodes.get(sel_nodes.size()-1));
			Node parent = sel_nodes.get(0).getParentNode();
			
			unlinkNodes(sel_nodes);
			
			if (prev_node == null) {
				// Append these elements to the end of the parent
				insertNodesInside(parent, sel_nodes);
			} else {
				// Insert before the next node
				insertNodesBefore(prev_node, sel_nodes);
			}
			
			fIsDirty = true;
			fTreeViewer.refresh();
			getEditor().editorDirtyStateChanged();
			updateParameterUpDownButtons();
		}
	}
	
	private void moveParameterDown() {
		List<Node> sel_nodes = getSelectedNodes();
		
		if (sel_nodes.size() > 0) {
			// TODO: need to detect when we have a heterogeneous selection
			Node next_node = getNextSiblingElement(sel_nodes.get(sel_nodes.size()-1));
			Node parent = sel_nodes.get(0).getParentNode();
			
			unlinkNodes(sel_nodes);
			
			if (next_node == null) {
				// Append these elements to the end of the parent
				insertNodesInside(parent, sel_nodes);
			} else {
				// Insert before the next node
				insertNodesAfter(next_node, sel_nodes);
			}
			
			fIsDirty = true;
			fTreeViewer.refresh();
			getEditor().editorDirtyStateChanged();
			updateParameterUpDownButtons();
		}		
	}
	
	private List<Node> getSelectedNodes() {
		List<Node> ret = new ArrayList<Node>();
		IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
		Iterator<Object> sel_it = sel.iterator();
		
		while (sel_it.hasNext()) {
			ret.add((Node)sel_it.next());
		}

		// Filter out category nodes
		while (ret.size() > 0 &&
				ret.get(0).getNodeName().equals("parameters") ||
				ret.get(0).getNodeName().equals("files")) {
			ret.remove(0);
		}
	
		// Filter out any nodes that don't match the root
		if (ret.size() > 0) {
			String root = ret.get(0).getNodeName();
			
			for (int i=1; i<ret.size(); i++) {
				if (!ret.get(i).getNodeName().equals(root)) {
					ret.remove(i);
					i--;
				}
			}
		}
		
		return ret;
	}
	
	private Node getNextSiblingElement(Node n) {
		while ((n = n.getNextSibling()) != null && 
				!(n instanceof Element)) {
		}
		
		return n;
	}

	private Node getPrevSiblingElement(Node n) {
		while ((n = n.getPreviousSibling()) != null && 
				!(n instanceof Element)) {
		}
		
		return n;
	}
	
	private void insertElement(Node active, String parent, Node new_elem) {
		if (active.getNodeName().equals(parent)) {
			// Insert the new node beneath the parent
			NodeList children = active.getChildNodes();
			if (children.getLength() == 0) {
				active.appendChild(new_elem);
			} else {
				Node first = children.item(0);
				active.insertBefore(new_elem, first);
			}
		} else {
			// Insert
			Node p_node = active.getParentNode();
			Node next = nextElement(active);
			
			if (next != null) {
				p_node.insertBefore(new_elem, next);
			} else {
				p_node.appendChild(new_elem);
			}
		}
	}
	
	private Node nextElement(Node active) {
		Node next = active;
		
		while ((next = next.getNextSibling()) != null &&
				!(next instanceof Element)) {
		}
		
		return next;
	}

	private SelectionListener selectionListener = new SelectionListener() {
		public void widgetDefaultSelected(SelectionEvent e) {}
		
		public void widgetSelected(SelectionEvent e) {
			if (!fSvtEditor.validateIsEditable()) {
				e.doit = false;
				return;
			}
			
			if (e.widget == fAddButton) {
				addElement();
			} else if (e.widget == fRemoveButton) {
				removeElement();
			} else if (e.widget == fUpButton) {
				moveTemplateUp();
			} else if (e.widget == fDownButton) {
				moveTemplateDown();
			} else if (e.widget == fAddParameterButton) {
				addParameter();
			} else if (e.widget == fAddParameterGroupButton) {
				addParameterGroup();
			} else if (e.widget == fRemoveParameterButton) {
				removeParameter();
			} else if (e.widget == fMoveParameterUpButton) {
				moveParameterUp();
			} else if (e.widget == fMoveParameterDownButton) {
				moveParameterDown();
			} else if (e.widget == fParameterGroupHidden) {
				setAttr(fActiveElement, "hidden", "" + fParameterGroupHidden.getSelection());
				fIsDirty = true;
				getEditor().editorDirtyStateChanged();
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
			} else if (fAttrMap.containsKey(e.widget)) {
				if (e.widget instanceof Button) {
					// Assume is a checkbox
					Button b = (Button)e.widget;
					setAttr(fActiveElement, fAttrMap.get(e.widget), 
							b.getSelection());
				}
			}
		}
	};
	
	private KeyListener keyListener = new KeyListener() {
		
		@Override
		public void keyReleased(KeyEvent e) {
			if (e.keyCode == SWT.DEL) {
//				System.out.println("DELETE");
			}
		}
		
		@Override
		public void keyPressed(KeyEvent e) { }
	};

	private ISelectionChangedListener selectionChangedListener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection ss = (IStructuredSelection)event.getSelection();
			
			if (ss.getFirstElement() == null) {
			} else if (ss.getFirstElement() instanceof String) {
				String e = (String)ss.getFirstElement();
				
				fAddButton.setEnabled(!fIsReadOnly);
				fRemoveButton.setEnabled(false);
				fUpButton.setEnabled(false);
				fDownButton.setEnabled(false);
				setDetailsPane(fNoDetailsPane);
				setButtonsPane(fDefaultButtons);
				
				fActiveElement = fDocument.createElement(e);
			} else {
				Element e = (Element)ss.getFirstElement();
				fActiveElement = e;
				if (e.getNodeName().equals("sv_template") ||
						e.getNodeName().equals("files")) {
					fAddButton.setEnabled(!fIsReadOnly);
					fRemoveButton.setEnabled(false);
					fUpButton.setEnabled(false);
					fDownButton.setEnabled(false);
					setDetailsPane(fNoDetailsPane);
					setButtonsPane(fDefaultButtons);
				} else if (e.getNodeName().equals("parameters")) {
					fAddButton.setEnabled(!fIsReadOnly);
					fRemoveButton.setEnabled(false);
					setDetailsPane(fNoDetailsPane);
					setButtonsPane(fParameterButtons);
				} else if (e.getNodeName().equals("template")) {
					setTemplateContext(e);
				} else if (e.getNodeName().equals("file")) {
					setFileContext(e);
				} else if (e.getNodeName().equals("parameter")) {
					setParameterContext(e);
				} else if (e.getNodeName().equals("group")) {
					setParameterGroupContext(e);
				} else if (e.getNodeName().equals("category")) {
					setCategoryContext(e);
				} else {
					// ??
				}
			}
		}
	};
	
	private VerifyListener verifyListener = new VerifyListener() {
		
		public void verifyText(VerifyEvent e) {
			// TODO Auto-generated method stub
			if (!fControlModify) {
				if (!fSvtEditor.validateIsEditable()) {
					e.doit = false;
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
	
	private class TemplateDragSource implements DragSourceListener {
		private TreeViewer			fViewer;
		
		public TemplateDragSource(TreeViewer viewer) {
			fViewer = viewer;
		}

		public void dragStart(DragSourceEvent event) { }

		public void dragSetData(DragSourceEvent event) {
			IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
			
			StringBuilder sel_sb = new StringBuilder();
			Iterator<Object> sel_it = sel.iterator();
			while (sel_it.hasNext()) {
				sel_sb.append(buildPath((Node)sel_it.next()));
				if (sel_it.hasNext()) {
					sel_sb.append("::;;::");
				}
			}
			
			event.data = sel_sb.toString();
		}

		public void dragFinished(DragSourceEvent event) { }
	}
	
	private String buildPath(Node n) {
		StringBuilder path = new StringBuilder();
		List<Node> hierarchy = new ArrayList<Node>();
		
		while (n != null) {
			if (n instanceof Element) {
				hierarchy.add(n);
			}
			n = n.getParentNode();
		}
		
		for (int i=hierarchy.size()-1; i>=0; i--) {
			Node e = hierarchy.get(i);
			String name = e.getNodeName();
			
			if (e instanceof Element) {
				Element el = (Element)e;
				if (el.hasAttribute("id")) {
					name += ":id=" + el.getAttribute("id");
				} else if (el.hasAttribute("name")) {
					name += ":name=" + el.getAttribute("name");
				}
			}
			path.append(name);
			
			if (i > 0) {
				path.append(";;::;;");
			}
		}
		
		return path.toString();
	}
	
	private class TemplateDropAdapter extends ViewerDropAdapter {
		
		public TemplateDropAdapter(Viewer viewer) {
			super(viewer);
		}

		@Override
		public boolean performDrop(Object data) {
			Element target = (Element)getCurrentTarget();
			int location = getCurrentLocation();
			int op = getCurrentOperation();
			List<Node> nodes = getNodesFromPath((String)data);

			if (target.getNodeName().equals("parameter") ||
					target.getNodeName().equals("parameters") ||
					target.getNodeName().equals("group")) {
				switch (location) {
					case LOCATION_ON: 
						if (target.getNodeName().equals("group")) {
							// Move the nodes inside the group
							unlinkNodes(nodes);
							insertNodesInside(target, nodes);
						}
						fIsDirty = true;
						break;
						
					case LOCATION_BEFORE:
						unlinkNodes(nodes);
						insertNodesBefore(target, nodes);
						fIsDirty = true;
						break;
						
					case LOCATION_AFTER:
						unlinkNodes(nodes);
						insertNodesAfter(target, nodes);
						fIsDirty = true;
						break;
				}
			}
			fTreeViewer.refresh();

			return true;
		}

		@Override
		public boolean validateDrop(
				Object 			target, 
				int 			operation,
				TransferData 	transferType) {
			DropTargetEvent event = getCurrentEvent();
			Object data = event.data;
			
			if (!(target instanceof Element)) {
				return false;
			}
			
			if (operation != DND.DROP_MOVE) {
				return false;
			}
			
			if (!fSvtEditor.validateIsEditable()) {
				return false;
			}
			
			// TODO Auto-generated method stub
			return true;
		}
	}
	
	private void unlinkNodes(List<Node> nodes) {
		for (Node n : nodes) {
			n.getParentNode().removeChild(n);
		}
	}
	
	private void insertNodesInside(Node parent, List<Node> nodes) {
		for (Node n : nodes) {
			parent.appendChild(n);
		}
	}
	
	private void insertNodesBefore(Node marker, List<Node> nodes) {
		Node parent = marker.getParentNode();
		for (Node n : nodes) {
			parent.insertBefore(n, marker);
		}
	}
	
	private void insertNodesAfter(Node marker, List<Node> nodes) {
		Node parent = marker.getParentNode();
		Node next_marker = marker;

		next_marker = getNextSiblingElement(marker);
		
		if (next_marker == null) {
			for (Node n : nodes) {
				parent.appendChild(n);
			}
		} else {
			for (Node n : nodes) {
				parent.insertBefore(n, next_marker);
			}
		}
	}
	
	private List<Node> getNodesFromPath(String path) {
		List<Node> ret = new ArrayList<Node>();
		List<String> paths = parsePathList(path);

		for (String p : paths) {
			List<Tuple<String, Map<String, String>>> selected = parseItem(p);
			Node n = findNode(fRoot, selected);
			ret.add(n);
		}
		
		return ret;
	}
	
	private List<String> parsePathList(String path) {
		List<String> ret = new ArrayList<String>();
		int idx = 0;
		int n_idx;
		
		while (true) {
			n_idx = path.indexOf("::;;::", idx);
			
			if (n_idx == -1) {
				// Done
				ret.add(path.substring(idx));
				break;
			} else {
				ret.add(path.substring(idx, n_idx));
				idx = n_idx+6;
			}
		}
		
		
		return ret;
	}
	
	private List<Tuple<String, Map<String, String>>> parseItem(String item) {
		List<Tuple<String, Map<String, String>>> ret = new ArrayList<Tuple<String,Map<String,String>>>();
		int idx = 0;
		int n_idx;
		
		while (true) {
			n_idx = item.indexOf(";;::;;", idx);
		
			String elem;
			if (n_idx == -1) {
				elem = item.substring(idx);
			} else {
				elem = item.substring(idx, n_idx);
				n_idx += 6;
			}
			
			Tuple<String, Map<String, String>> elem_p = parseElem(elem);
			ret.add(elem_p);
			
			if (n_idx == -1) {
				break;
			}
			idx = n_idx;
		}
		
		return ret;
	}
	
	private Tuple<String, Map<String, String>> parseElem(String elem) {
		String name;
		String key=null, val=null;
		Map<String, String> map = new HashMap<String, String>();
		
		int idx = elem.indexOf(":");
		
		if (idx == -1) {
			name = elem;
		} else {
			name = elem.substring(0, idx);
			int eq_idx = elem.indexOf("=", idx);
			key = elem.substring(idx+1, eq_idx);
			val = elem.substring(eq_idx+1);
		}
	
		if (key != null) {
			map.put(key, val);
		}
	
		return new Tuple<String, Map<String,String>>(name, map);
	}
	
	private Node findNode(Element root, List<Tuple<String, Map<String, String>>> path) {
		Node node = root;
		Node ret = null;
		
		for (int i=0; i<path.size(); i++) {
			Tuple<String, Map<String, String>> p = path.get(i);
			
			if (i == 0) {
				if (!p.first().equals(node.getNodeName())) {
					break;
				}
			} else {
				Node next_node = null;
				NodeList nl = node.getChildNodes();
				for (int j=0; j<nl.getLength(); j++) {
					Node n = nl.item(j);
					if (n instanceof Element && n.getNodeName().equals(p.first())) {
						Element el = (Element)n;
						// See all attributes are present
						boolean match = true;
						for (Entry<String, String> e : p.second().entrySet()) {
							if (!el.hasAttribute(e.getKey()) || 
									!el.getAttribute(e.getKey()).equals(e.getValue())) {
								match = false;
								break;
							}
						}
						
						if (match) {
							next_node = n;
							break;
						}
					}
				}
				
				if (next_node == null) {
					break;
				}
				node = next_node;
			}
			
			if (i+1 == path.size()) {
				ret = node;
			}
		}
		
		return ret;
	}
	
	private void setAttr(Element elem, String attr, String value) {
		elem.setAttribute(attr, value);
	}

	private void setAttr(Element elem, String attr, boolean value) {
		elem.setAttribute(attr, "" + value);
	}
	
	private void setElem(Element elem, String e_name, String value) {
		NodeList nl = elem.getChildNodes();
		Element e = null;
		
		for (int i=0; i<nl.getLength(); i++) {
			if (nl.item(i) instanceof Element &&
					nl.item(i).getNodeName().equals(e_name)) {
				e = (Element)nl.item(i);
				break;
			}
		}
		
		if (e == null) {
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
	
	private boolean getBooleanAttribute(Element elem, String attr, boolean dflt) {
		if (elem.hasAttribute(attr)) {
			String val = elem.getAttribute(attr);
			return val.equals("true");
		} else {
			return dflt;
		}
	}

	private String getAttribute(Element elem, String attr, String dflt) {
		String ret = elem.getAttribute(attr);
		
		if (ret == null) {
			ret = dflt;
		}
		
		return ret;
	}

	private String getElementText(Element elem, String c_elem) {
		String ret = "";
		NodeList nl = elem.getChildNodes();
		
		for (int i=0; i<nl.getLength(); i++) {
			if (nl.item(i).getNodeName().equals(c_elem) &&
					nl.item(i) instanceof Element) {
				ret = nl.item(i).getTextContent();
				break;
			}
		}
		
		return ret;
	}
	
	private List<Element> getElements(NodeList nl) {
		List<Element> el_l = new ArrayList<Element>();
		for (int i=0; i<nl.getLength(); i++) {
			Node n = nl.item(i);
			if (n instanceof Element) {
				el_l.add((Element)n);
			}
		}

		return el_l;
	}

}
