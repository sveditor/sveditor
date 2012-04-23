package net.sf.sveditor.core.templates;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

public class WSInStreamProvider implements ITemplateInStreamProvider {

	public InputStream openStream(String path) {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		InputStream in = null;
		
		try {
			IFile file = root.getFile(new Path(path));
			
			if (file.exists()) {
				in = file.getContents();
			}
		} catch (CoreException e) {}
		
		return in;
	}

	public void closeStream(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}

}
