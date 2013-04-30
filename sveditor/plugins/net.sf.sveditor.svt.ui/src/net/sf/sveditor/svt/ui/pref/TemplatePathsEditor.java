package net.sf.sveditor.svt.ui.pref;


import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.PathEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;

public class TemplatePathsEditor extends PathEditor {
	
	public TemplatePathsEditor(String name, Composite parent) {
		super(name, "SV Template Paths", "Browse", parent);
	}

	@Override
	protected String getNewInputObject() {
		AddDirectoryPathDialog prefs = new AddDirectoryPathDialog(getShell(), SWT.SHEET);
		
		String dir = null;
		
		if (prefs.open() == Dialog.OK) {
			dir = prefs.getPath();
		} 
		
		return dir;
	}
}
