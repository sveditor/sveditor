package net.sf.sveditor.core;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class SVDBPluginLibIndex implements ISVDBIndex {
	private Bundle					fBundle;
	private String					fRoot;
	private String					fPluginNS;
	private Map<File, SVDBFile>		fFileList;
	private boolean					fFileListValid;
	
	private Map<File, SVDBFile>		fFileIndex;
	private boolean					fFileIndexValid;
	private ISVDBIndex				fSuperIndex;
	
	public SVDBPluginLibIndex(
			String				name,
			String				plugin_namespace,
			String				root) {
		fPluginNS = plugin_namespace;
		fBundle = Platform.getBundle(fPluginNS);
		fRoot   = root;
		
		fFileList = new HashMap<File, SVDBFile>();
		fFileIndex = new HashMap<File, SVDBFile>();
		
		// getPreProcFileMap();
		getFileDB();
	}
	
	public SVDBFile findPreProcFile(File path) {
		Map<File, SVDBFile> map = getPreProcFileMap();
			
		return map.get(path);
	}

	public SVDBFile findFile(File path) {
		Map<File, SVDBFile> map = getFileDB();
		
		return map.get(path);
	}

	public SVDBFile findIncludedFile(String leaf) {
		Map<File, SVDBFile> map = getPreProcFileMap();
		
		Iterator<File> it = map.keySet().iterator();
		
		while (it.hasNext()) {
			File f = it.next();
			
			if (f.getPath().endsWith(leaf)) {
				return map.get(f);
			}
		}
		
		return null;
	}

	public File getBaseLocation() {
		return new File("plugin:/" + fPluginNS + "/" + fRoot);
	}

	public void setSuperIndex(ISVDBIndex index) {
		fSuperIndex = index;
	}
	
	public ISVDBIndex getSuperIndex() {
		return fSuperIndex;
	}
	
	public synchronized Map<File, SVDBFile> getFileDB() {
		if (!fFileIndexValid) {
			buildIndex();
		}
		
		return fFileIndex;
	}

	public int getIndexType() {
		return ISVDBIndex.IT_BuildPath;
	}

	public Map<File, SVDBFile> getPreProcFileMap() {
		if (!fFileListValid) {
			buildPreProcFileMap();
		}
		
		return fFileList;
	}
	
	@SuppressWarnings("unchecked")
	private synchronized void buildPreProcFileMap() {
		String root_dir = new File(fRoot).getParent();
		
		Enumeration<URL> entries = 
			(Enumeration<URL>)fBundle.findEntries(root_dir, "*", true);
		
		while (entries.hasMoreElements()) {
			URL url = entries.nextElement();
			SVPreProcScanner sc = new SVPreProcScanner();
			SVDBPreProcObserver ob = new SVDBPreProcObserver();

			// Check whether this entry is a directory
			if (url.getFile().endsWith("/")) {
				continue;
			}
			
			sc.setObserver(ob);
			
			try {
				InputStream in = url.openStream();
				File f = new File("plugin:/" + fPluginNS + "/" + url.getPath());
				
				sc.init(in, f.getPath());
				sc.scan();
				
				SVDBFile file = ob.getFiles().get(0);
				
				if (fFileList.containsKey(f)) {
					fFileList.remove(f);
				}
				fFileList.put(f, file);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		fFileListValid = true;
	}
	
	@SuppressWarnings("unchecked")
	private synchronized void buildIndex() {
		File root_f = new File(fRoot);
		
		Enumeration<URL> entries = (Enumeration<URL>)fBundle.findEntries(
				root_f.getParent(),	root_f.getName(), false);
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		
		URL root = entries.nextElement();
		
		File f = new File("plugin:/" + fPluginNS + "/" + root.getPath());
		SVDBFile pp_file = findPreProcFile(f);
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		prepareFileTree(ft_root, null);
		processFile(ft_root, dp);
		
		fFileIndexValid = true;
	}
	
	@SuppressWarnings("unchecked")
	private void processFile(
			SVDBFileTree 				path,
			SVPreProcDefineProvider		dp) {
		dp.setFileContext(path);
		
		SVDBFileFactory scanner = new SVDBFileFactory(dp);
		
		String path_s = path.getFilePath().getPath();
		
		path_s = path_s.substring("plugin:/".length());
		path_s = path_s.substring(path_s.indexOf('/'));
		
		File path_f = new File(path_s);

		Enumeration<URL> entries = (Enumeration<URL>)fBundle.findEntries(
				path_f.getParent(), path_f.getName(), false);
		
		try {
			URL url = entries.nextElement();
			InputStream in = url.openStream();
			SVDBFile svdb_f = scanner.parse(in, path.getFilePath().getPath());

			fFileIndex.put(path.getFilePath(), svdb_f);
		} catch (IOException e) {
			e.printStackTrace();
		}

		// Now, recurse through the files included
		for (SVDBFileTree ft_t : path.getIncludedFiles()) {
			if (!fFileIndex.containsKey(ft_t.getFilePath())) {
				processFile(ft_t, dp);
			}
		}
	}
	

	public void rebuildIndex() {}

	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	public void addChangeListener(ISVDBIndexChangeListener l) {}

	public void dispose() {}
	
	private void prepareFileTree(
			SVDBFileTree 				root,
			SVDBFileTree				parent) {
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
		
		ft_utils.setIndex(fSuperIndex);
		
		ft_utils.resolveConditionals(root);
		
		if (parent != null) {
			root.getIncludedByFiles().add(parent);
		}
		
		addIncludeFiles(root, root.getSVDBFile());
	}
	
	private void addIncludeFiles(
			SVDBFileTree 		root, 
			SVDBScopeItem 		scope) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Include) {
				SVDBFile f = new SVDBIncludeSearch(this).findIncludedFile(it.getName());

				SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.duplicate());
				root.getIncludedFiles().add(ft);
				
				prepareFileTree(ft, root);
			} else if (it instanceof SVDBScopeItem) {
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}
}
