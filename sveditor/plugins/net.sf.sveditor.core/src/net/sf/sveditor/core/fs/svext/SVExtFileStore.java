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

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVExtFileStore extends FileStore {
	private SVExtFileStore					fParent;
	private Map<String, SVExtFileStore>		fChildren;
	private String							fPath;
	private FileInfo						fInfo;
	// File that corresponds to this element
	private File							fFile;
	private static boolean					fDebugEn;
	private static LogHandle				fLog;
	
	static {
		fLog = LogFactory.getLogHandle("SVExtFileStore");
		fLog.addLogLevelListener(new ILogLevelListener() {
			
			@Override
			public void logLevelChanged(ILogHandle handle) {
				fDebugEn = handle.isEnabled();
			}
		});
		fDebugEn = fLog.isEnabled();
	}

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
	
		fParent = parent;
		fFile = file;
		
		fInfo = new FileInfo(name);
		fInfo.setDirectory(is_dir);
		fInfo.setExists(true);
		fInfo.setLength(EFS.NONE);

		if (fDebugEn) {
			fLog.debug("SVExtFileStore: path=" + path + " name=" + name + " file=" + file);
		}
	}
	
	public Map<String, SVExtFileStore> getChildren() {
		return fChildren;
	}

	@Override
	public String[] childNames(int options, IProgressMonitor monitor) throws CoreException {
		Set<String> keys = fChildren.keySet();
		return keys.toArray(new String[keys.size()]);
	}

	@Override
	public IFileInfo fetchInfo(int options, IProgressMonitor monitor) throws CoreException {
		return fInfo;
	}

	@Override
	public IFileStore getChild(String name) {
		IFileStore ret = null;
		if (fChildren.containsKey(name)) {
			ret = fChildren.get(name);
		} else {
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
			} else {
				File file = new File(fFile, name);
				// Build path from here
				ret = new SVExtFileStore(
						this,
						fPath + "/" + fInfo.getName(),
						name,
						file,
						file.isDirectory());
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
		if (fDebugEn) {
			fLog.debug("openInputStream: " + fFile);
		}
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
//				uri = new URI("file://" + fFile.getAbsolutePath().replace('\\', '/'));
//			}
		} catch (URISyntaxException e) { 
			e.printStackTrace();
		}
		if (fDebugEn) {
			fLog.debug("toURI: file=" + fFile + " uri=" + uri);
		}
		return uri;
	}

//	@Override
//	public File toLocalFile(int options, IProgressMonitor monitor) throws CoreException {
//		// TODO Auto-generated method stub
//		File ret = super.toLocalFile(options, monitor);
////		System.out.println("toLocalFile: options=" + options + " " + fFile + "(" + ret + ")");
//		return ret;
//	}
	
	

}
