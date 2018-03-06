package net.sf.sveditor.core.fs.svext;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileInfo;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileInfo;
import org.eclipse.core.filesystem.provider.FileStore;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import com.sun.org.apache.bcel.internal.generic.FNEG;

import net.sf.sveditor.core.SVFileUtils;

public class SVExtFileStore extends FileStore {
	private SVExtFileStore					fParent;
	private Map<String, SVExtFileStore>		fChildren;
	private String							fPath;
	private FileInfo						fInfo;
	// File that corresponds to this element
	private File							fFile;

	public SVExtFileStore(String path) {
		fPath = path;
		fChildren = new HashMap<String, SVExtFileStore>();
		fInfo = new FileInfo(path);
		fInfo.setDirectory(true);
		fInfo.setExists(true);
		fInfo.setLength(EFS.NONE);
	}
	
	public SVExtFileStore(
			SVExtFileStore	parent, 
			String 			path, 
			String 			name,
			File			file,
			boolean			is_dir) {
		this(path);
		
		System.out.println("SVExtFileStore: dir=" + name);
		
		fParent = parent;
		fFile = file;
		
		fInfo = new FileInfo(name);
		fInfo.setDirectory(is_dir);
		fInfo.setExists(true);
		fInfo.setLength(EFS.NONE);
	}
	
	public Map<String, SVExtFileStore> getChildren() {
		return fChildren;
	}

	@Override
	public String[] childNames(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println(fInfo.getName() + ": childNames");
		Set<String> keys = fChildren.keySet();
		for (String child : keys) {
			System.out.println("  " + child);
		}
		return keys.toArray(new String[keys.size()]);
	}

	@Override
	public IFileInfo fetchInfo(int options, IProgressMonitor monitor) throws CoreException {
		System.out.println(fInfo.getName() + ": fetchInfo");
		return fInfo;
	}

	@Override
	public IFileStore getChild(String name) {
		IFileStore ret = null;
		System.out.println(fInfo.getName() + ": getChild: " + name);
		if (fChildren.containsKey(name)) {
			ret = fChildren.get(name);
		} else {
			System.out.println("  not in root: parent=" + fParent);
			System.out.println("    path=" + fPath + "/" + name);
			// Go ahead create anonymous files to represent the path
			if (fParent == null) {
				// Root
				File root = null;
				if (SVFileUtils.isWin()) {
					root = new File(name + ":/");
				} else {
					root = new File("/" + name);
				}
		
				ret = new SVExtFileStore(
						this,
						fPath /*+ "/" + name */,
						name,
						root,
						true);
				System.out.println("Root: fPath=" + fPath + " name=" + name + " uri=" +
						ret.toURI());
			} else {
				File file = new File(fFile, name);
				// Build path from here
				ret = new SVExtFileStore(
						this,
						fPath + "/" + fInfo.getName(),
						name,
						file,
						file.isDirectory());
				System.out.println("NonRoot: fPath=" + fPath + " name=" + name + " uri=" +
						ret.toURI());
			}
		}
		return ret;
	}

	@Override
	public String getName() {
		return fInfo.getName();
	}

	@Override
	public IFileStore getParent() {
		return fParent;
	}

	@Override
	public InputStream openInputStream(int options, IProgressMonitor monitor) throws CoreException {
		InputStream in = null;
		if (fFile != null && fFile.isFile()) {
			try {
				in = new FileInputStream(fFile);
			} catch (IOException e) { }
		}
		return in;
	}

	@Override
	public OutputStream openOutputStream(int options, IProgressMonitor monitor) throws CoreException {
		OutputStream os = null;
		if (fFile != null && fFile.isFile()) {
			try {
				os = new FileOutputStream(fFile);
			} catch (IOException e) { }
		}
		return os;
	}

	@Override
	public URI toURI() {
		URI uri = null;
		try {
//			if (fFile != null) {
//				uri = new URI("file://" + fFile.getAbsolutePath());
//			} else {
				uri = new URI("svext://" + fPath + "/" + fInfo.getName());
//			}
		} catch (URISyntaxException e) { }
		return uri;
	}

}
