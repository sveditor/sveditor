package net.sf.sveditor.ui.svt.editor;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;

public class TextEditorPage extends TextEditor implements IFormPage {
	private SVTEditor				fEditor;
	private Control					fPartControl;
	private int					fIndex;
	private boolean				fIsActive;
	
	public TextEditorPage() {
		setPartName("Source");
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

}
