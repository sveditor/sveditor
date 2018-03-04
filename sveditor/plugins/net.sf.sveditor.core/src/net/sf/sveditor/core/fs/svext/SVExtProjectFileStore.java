package net.sf.sveditor.core.fs.svext;

import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileInfo;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileInfo;
import org.eclipse.core.filesystem.provider.FileStore;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import net.sf.sveditor.core.db.project.SVDBProjectData;

public class SVExtProjectFileStore extends FileStore {
	private SVDBProjectData				fProjData;
	
	public SVExtProjectFileStore(SVDBProjectData pd) {
		fProjData = pd;
	}
	
	@Override
	public String[] childNames(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("childNames");
		return new String[0];
	}

	@Override
	public IFileInfo fetchInfo(int options, IProgressMonitor monitor) throws CoreException {
		FileInfo ret = new FileInfo(fProjData.getName());
		ret.setExists(true);
		ret.setDirectory(true);
		ret.setLength(EFS.NONE);
		System.out.println("fetchInfo");
		// TODO Auto-generated method stub
		return ret;
	}

	@Override
	public IFileStore getChild(String name) {
		System.out.println("getChild");
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getName() {
		System.out.println("getName");
		// TODO Auto-generated method stub
		return fProjData.getName();
	}

	@Override
	public IFileStore getParent() {
		System.out.println("getParent");
		return null;
	}

	@Override
	public InputStream openInputStream(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("openInputStream");
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public IFileInfo[] childInfos(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("childInfos");
		// TODO Auto-generated method stub
		return super.childInfos(options, monitor);
	}

	@Override
	public IFileStore[] childStores(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println("childStores");
		// TODO Auto-generated method stub
		return super.childStores(options, monitor);
	}

	@Override
	public URI toURI() {
		System.out.println("toURI");
		URI uri = null;
		try {
			uri = new URI("svext://" + fProjData.getName());
		} catch (URISyntaxException e) { }
		
		return uri;
	}

}
