package net.sf.sveditor.core.db.index;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBWSFileSystemOutputStream extends ByteArrayOutputStream {
	private IFile				fFile;
	
	public SVDBWSFileSystemOutputStream(IFile file) {
		fFile = file;
	}

	@Override
	public void close() throws IOException {
		ByteArrayInputStream bin = new ByteArrayInputStream(toByteArray());

		for (int i=0; i<2; i++) {
			try {
				if (fFile.exists()) {
					fFile.setContents(bin, true, true, new NullProgressMonitor());
				} else {
					fFile.create(bin, true, new NullProgressMonitor());
				}				
				break;
			} catch (CoreException e) {
				// Often times, we can just refresh the resource to avoid
				// an indexing failure
				if (i == 0 && e.getMessage().contains("out of sync")) {
					try {
						fFile.getParent().refreshLocal(IResource.DEPTH_INFINITE, null);
					} catch (CoreException e2) {}
				} else {
					throw new IOException("Failed to set file contents: " + e.getMessage());
				}
			}
		}
	}

}
