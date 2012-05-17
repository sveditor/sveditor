package net.sf.sveditor.ui;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;

public class EditorInputUtils {
	
	public static InputStream openInputStream(IEditorInput input) {
		InputStream in = null;
		
		if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			try {
				in = new FileInputStream(uri.getPath());
			} catch (IOException e) {
				e.printStackTrace();
			}
		} else if (input instanceof IFileEditorInput) {
			IFile file = ((IFileEditorInput)input).getFile();
			try {
				in = file.getContents();
			} catch (CoreException e) {}
		}
		
		return in;
	}

}
