package net.sf.sveditor.ui.argfile.editor;

import net.sf.sveditor.core.log.ILogLevel;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.TextEditor;

public class SVArgFileEditor extends TextEditor implements ILogLevel {
	private SVArgFileCodeScanner			fCodeScanner;
	
	public SVArgFileEditor() {
		fCodeScanner = new SVArgFileCodeScanner();
		
	}

	
	public SVArgFileCodeScanner getCodeScanner() {
		return fCodeScanner;
	}


	@Override
	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new SVArgFileSourceViewerConfiguration(this));

		super.createPartControl(parent);
	}
	
	
	
}
