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
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.osgi.framework.Bundle;

public class SVDBPluginLibIndex implements ISVDBIndex {
	private Bundle					fBundle;
	private String					fRoot;
	private Map<File, SVDBFile>		fFileList;
	private boolean					fFileListValid;
	
	private Map<File, SVDBFile>		fFileIndex;
	private boolean					fFileIndexValid;
	
	public SVDBPluginLibIndex(
			String				name,
			Bundle				resource_bundle,
			String				root) {
		fBundle = resource_bundle;
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
		System.out.println("[FIXME] getBaseLocation()");
		return null;
	}

	public synchronized Map<File, SVDBFile> getFileDB() {
		if (!fFileIndexValid) {
			buildIndex();
		}
		
		return fFileIndex;
	}

	public int getIndexType() {
		// TODO Auto-generated method stub
		return 0;
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
		
		long start = System.currentTimeMillis();
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
				
				sc.init(in, url.getPath());
				sc.scan();
				
				SVDBFile file = ob.getFiles().get(0);
				
				File f = new File(url.getPath());
				if (fFileList.containsKey(f)) {
					fFileList.remove(f);
				}
				fFileList.put(f, file);
			} catch (IOException e) {
				e.printStackTrace();
				System.out.println("path=" + url.getPath() + 
						" file=" + url.getFile() + 
						" protocol=" + url.getProtocol());
			}
		}
		long end = System.currentTimeMillis();
		
		System.out.println("find-files: " + (end-start));

		fFileListValid = true;
	}
	
	@SuppressWarnings("unchecked")
	private synchronized void buildIndex() {
		File root_f = new File(fRoot);
		
		Enumeration<URL> entries = (Enumeration<URL>)fBundle.findEntries(
				root_f.getParent(),	root_f.getName(), false);
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		
		URL root = entries.nextElement();
		
		SVDBFile pp_file = findPreProcFile(new File(root.getPath()));
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		long start = System.currentTimeMillis();
		prepareFileTree(ft_root, null);
		
		processFile(ft_root, dp);
		
		long end = System.currentTimeMillis();
		
		System.out.println("build index took: " + (end-start));
		
		fFileIndexValid = true;
	}
	
	@SuppressWarnings("unchecked")
	private void processFile(
			SVDBFileTree 				path,
			SVPreProcDefineProvider		dp) {
		dp.setFileContext(path);
		
		SVDBFileFactory scanner = new SVDBFileFactory(dp);

		Enumeration<URL> entries = (Enumeration<URL>)fBundle.findEntries(
				path.getFilePath().getParent(), path.getFilePath().getName(), false);
		
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
				SVDBFile f = findIncludedFile(it.getName());

				SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.duplicate());
				root.getIncludedFiles().add(ft);
				
				prepareFileTree(ft, root);
			} else if (it instanceof SVDBScopeItem) {
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}
}
