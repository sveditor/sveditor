package net.sf.sveditor.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;

public class SVEditorDocumentProvider extends TextFileDocumentProvider {
	private static SVEditorDocumentProvider		fDefault;
	
	protected FileInfo createFileInfo(Object elem) throws CoreException {
		FileInfo result = super.createFileInfo(elem);
		setUpSynchronization(result);
		
		return result;
	}

	public static synchronized SVEditorDocumentProvider getDefault() {
		if (fDefault == null) {
			fDefault = new SVEditorDocumentProvider();
		}
		return fDefault;
	}
}
