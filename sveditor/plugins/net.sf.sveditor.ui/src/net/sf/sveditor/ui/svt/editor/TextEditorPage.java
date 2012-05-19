package net.sf.sveditor.ui.svt.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;

public class TextEditorPage extends TextEditor implements IFormPage {
	private SVTEditor				fEditor;
	private Control					fPartControl;
	private int					fIndex;
	private boolean				fIsActive;
	private boolean				fIsDirty;
	
	public TextEditorPage() {
		setPartName("Source");
	}

	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		// TODO Auto-generated method stub
		super.init(site, input);
		getDocumentProvider().getDocument(input).addDocumentListener(
				documentListener);
	}

	@Override
	public void doSave(IProgressMonitor progressMonitor) {
		System.out.println("doSave");
		// TODO Auto-generated method stub
		super.doSave(progressMonitor);
	}

	public void initialize(FormEditor editor) {
		fEditor = (SVTEditor)editor;
	}

	public FormEditor getEditor() {
		return fEditor;
	}

	public IManagedForm getManagedForm() {
		return null;
	}

	public void setActive(boolean active) {
		fIsActive = active;
	}

	public boolean isActive() {
		return fIsActive;
	}
	
	@Override
	public boolean isDirty() {
		return fIsDirty;
	}

	public boolean canLeaveThePage() {
		return true;
	}
	
	public void createPartControl(Composite parent) {
		super.createPartControl(parent);
		
		Control children[] = parent.getChildren();
		fPartControl = children[children.length-1];
	}

	public Control getPartControl() {
		return fPartControl;
	}

	public String getId() {
		// TODO Auto-generated method stub
		return null;
	}

	public int getIndex() {
		return fIndex;
	}

	public void setIndex(int index) {
		fIndex = index;
	}

	public boolean isEditor() {
		return true;
	}

	public boolean selectReveal(Object object) {
		// TODO Auto-generated method stub
		return false;
	}

	private IDocumentListener documentListener = new IDocumentListener() {
		
		public void documentChanged(DocumentEvent event) {
			fIsDirty = true;
			getEditor().editorDirtyStateChanged();
		}
		
		public void documentAboutToBeChanged(DocumentEvent event) {}
	};
}
