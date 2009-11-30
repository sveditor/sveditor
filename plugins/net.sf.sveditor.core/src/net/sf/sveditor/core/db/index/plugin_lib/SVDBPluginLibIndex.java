package net.sf.sveditor.core.db.index.plugin_lib;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBFileSystemChangeListener;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;

import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class SVDBPluginLibIndex extends SVDBLibIndex implements ISVDBFileSystemProvider {
	private Bundle					fBundle;
	private String					fPluginNS;
	private String					fRootFile;
	
	public SVDBPluginLibIndex(
			String 			project, 
			String 			base_location) {
		super(project, base_location, null);
		
		fFileSystemProvider = this;
		
		System.out.println("SVDBPluginLibIndex: 2-arg");

		base_location = base_location.substring("plugin:/".length());
		
		fPluginNS = base_location.substring(0, base_location.indexOf('/'));
		base_location = base_location.substring(base_location.indexOf('/')+1);
		fRootFile = base_location.substring(base_location.indexOf('/')-1);
		fBundle = Platform.getBundle(fPluginNS);
		
		System.out.println("RootFile: " + fRootFile + " Root: " + fRoot);
		
		fFileList = new HashMap<String, SVDBFile>();
		fFileIndex = new HashMap<String, SVDBFile>();
	}
	
	public SVDBPluginLibIndex(
			String 			project, 
			String			plugin_ns,
			String			root) {
		super(project, "plugin:/" + plugin_ns + "/" + root, null);

		fFileSystemProvider = this;

		System.out.println("SVDBPluginLibIndex: 3-arg");

		fRootFile = root;
		fPluginNS = plugin_ns;
		
		if (!root.startsWith("/")) {
			root = "/" + root;
		}
		fBundle = Platform.getBundle(fPluginNS);
		
		
		
		fFileList = new HashMap<String, SVDBFile>();
		fFileIndex = new HashMap<String, SVDBFile>();
	}
	
	public String getTypeID() {
		return SVDBPluginLibIndexFactory.TYPE;
	}
	
	@SuppressWarnings("unchecked")
	protected List<String> getFileList() {
		String root_dir = new File(fRootFile).getParent();
		List<String> ret = new ArrayList<String>();
		
		Enumeration<URL> entries = 
			(Enumeration<URL>)fBundle.findEntries(root_dir, "*", true);
		
		if (entries == null) {
			System.out.println("Failed to find bundle entry \"" + root_dir + "\"");
		}
		
		while (entries.hasMoreElements()) {
			URL url = entries.nextElement();
			
			if (url.getFile().endsWith("/")) {
				continue;
			}
			
			String ext = "";
			String path = url.getFile(); 
			if (path.lastIndexOf('.') != -1) {
				ext = path.substring(path.lastIndexOf('.'));
			}
			
			if (!fSVExtensions.contains(ext)) {
				continue;
			}

			boolean ignore = false;
			for (String ignore_dir : fIgnoreDirs) {
				if (path.contains(ignore_dir)) {
					ignore = true;
					break;
				}
			}
			
			if (ignore) {
				continue;
			}

			String full_path = "plugin:/" + fPluginNS + path;
			
			ret.add(full_path);
		}
		
		return ret;
	}
	
	public void closeStream(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}

	public boolean fileExists(String path) {
 		if (path.startsWith("plugin:/")) {

			String leaf = path.substring(("plugin:/" + fPluginNS).length());

			return (fBundle.getEntry(leaf) != null);
		} else {
			return false;
		}
	}

	// Init for ISVDBFileSystem interface
	public void init(String root) {}

	public InputStream openStream(String path) {
		InputStream ret = null;
		
		if (path.startsWith("plugin:/")) {

			String leaf = path.substring(("plugin:/" + fPluginNS).length());

			URL url = fBundle.getEntry(leaf);

			if (url != null) {
				try {
					ret = url.openStream();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		
		return ret;
	}
	
	public long getLastModifiedTime(String file) {
		return fBundle.getLastModified();
	}
	
	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}
	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}


	public void rebuildIndex() {}

	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	public void addChangeListener(ISVDBIndexChangeListener l) {}

	public void dispose() {}
	
}
