package net.sf.sveditor.ui;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;

import net.sf.sveditor.core.Tuple;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;

public class EditorInputUtils {
	
	public static Tuple<File, IFile> getFileLocation(IEditorInput input) {
		File file = null;
		IFile ifile = null;
		
		if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			file = new File(uri.getPath());
		} else if (input instanceof IFileEditorInput) {
			ifile = ((IFileEditorInput)input).getFile();
		}
		
		return new Tuple<File, IFile>(file, ifile);
	}
	
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

	public static void setContents(IEditorInput input, InputStream in) throws Exception {
		
		if (input instanceof IURIEditorInput) {
			OutputStream out = null;
			URI uri = ((IURIEditorInput)input).getURI();
			byte tmp[] = new byte[4096];
			int len;
			
			out = new FileOutputStream(uri.getPath());
			
			while ((len = in.read(tmp, 0, tmp.length)) > 0) {
				out.write(tmp, 0, len);
			}
			out.close();
		} else if (input instanceof IFileEditorInput) {
			IFile file = ((IFileEditorInput)input).getFile();
			file.setContents(in, true, true, new NullProgressMonitor());
		}
	}
}
