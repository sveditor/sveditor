package net.sf.sveditor.core.fs.svext;

import java.io.InputStream;
import java.net.URI;

import org.eclipse.core.filesystem.IFileInfo;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileStore;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

public class SVExtFileStore extends FileStore {
	
	public SVExtFileStore(URI uri) {
		
	}

	@Override
	public String[] childNames(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("childNames");
		return new String[] {"a", "b", "c"};
	}

	@Override
	public IFileInfo fetchInfo(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("fetchInfo");
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IFileStore getChild(String name) {
		System.out.println("getChild: " + name);
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getName() {
		System.out.println("getName");
		return null;
	}

	@Override
	public IFileStore getParent() {
		System.out.println("getParent");
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public InputStream openInputStream(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("openInputStream");
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public URI toURI() {
		System.out.println("toURI");
		// TODO Auto-generated method stub
		return null;
	}

}
