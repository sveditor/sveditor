package net.sf.sveditor.core.db.index;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

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
	private ISVDBIndexRegistry		fIndexRegistry;
	private static Pattern			fWinPathPattern = Pattern.compile("\\\\");
	protected static final List<String>			fSVExtensions;
	protected static final List<String>			fIgnoreDirs;
	
	
	static {
		fSVExtensions = new ArrayList<String>();
		
		fSVExtensions.add(".sv");
		fSVExtensions.add(".svh");
		fSVExtensions.add(".v");
		fSVExtensions.add(".V");
		fSVExtensions.add(".vl");
		fSVExtensions.add(".vlog");
		
		fIgnoreDirs = new ArrayList<String>();
		fIgnoreDirs.add("/.svn/");
		fIgnoreDirs.add("/CVS/");
		
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	public SVDBPluginLibIndex(String base_location) {
		base_location = base_location.substring("plugin:/".length());
		
		fPluginNS = base_location.substring(0, base_location.indexOf('/'));
		System.out.println("fPluginNS=" + fPluginNS);
		
		fRoot = base_location.substring(base_location.indexOf('/'));
		System.out.println("fRoot=" + fRoot);
		
		fBundle = Platform.getBundle(fPluginNS);
		
		fFileList = new HashMap<File, SVDBFile>();
		fFileIndex = new HashMap<File, SVDBFile>();
	}
	
	/*
	public SVDBPluginLibIndex(
			String				name,
			String				plugin_namespace,
			String				root) {
		fPluginNS = plugin_namespace;
		fBundle = Platform.getBundle(fPluginNS);
		fRoot   = root;
		
		fFileList = new HashMap<File, SVDBFile>();
		fFileIndex = new HashMap<File, SVDBFile>();
	}
	 */
	
	public void init(ISVDBIndexRegistry registry) {
		fIndexRegistry = registry;
	}
	
	public String getTypeID() {
		return ISVDBIndexFactory.TYPE_PluginLibIndex;
	}
	
	public boolean isLoaded() {
		return (fFileIndexValid && fFileListValid);
	}
	
	public void load(List<SVDBFile> pp_files, List<SVDBFile> db_files) {
		System.out.println("SVDBPluginLibIndex.load()");
		
		fFileList.clear();
		fFileIndex.clear();
		
		for (SVDBFile f : pp_files) {
			fFileList.put(f.getFilePath(), f);
		}
		
		for (SVDBFile f : db_files) {
			fFileList.put(f.getFilePath(), f);
		}
		
		fFileIndexValid = true;
		fFileListValid  = true;
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
			
			String norm_path = fWinPathPattern.matcher(f.getPath()).replaceAll("/");
			
			if (norm_path.endsWith(leaf)) {
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
			if (!fIndexRegistry.loadPersistedData(this)) {
				buildIndex();
			}
		}
		
		return fFileIndex;
	}

	public int getIndexType() {
		return ISVDBIndex.IT_BuildPath;
	}

	public synchronized Map<File, SVDBFile> getPreProcFileMap() {
		if (!fFileListValid) {
			if (!fIndexRegistry.loadPersistedData(this)) {
				buildPreProcFileMap();
			}
		}
		
		return fFileList;
	}
	
	@SuppressWarnings("unchecked")
	private synchronized void buildPreProcFileMap() {
		System.out.println("--> buildPreProcFileMap()");
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
		System.out.println("<-- buildPreProcFileMap()");
	}
	
	@SuppressWarnings("unchecked")
	private synchronized void buildIndex() {
		System.out.println("--> buildIndex()");
		long start = System.currentTimeMillis();
		File root_f = new File(fRoot);
		
		Enumeration<URL> entries = (Enumeration<URL>)fBundle.findEntries(
				root_f.getParent(),	root_f.getName(), false);
		SVPreProcDefineProvider		dp = new SVPreProcDefineProvider();
		
		URL root = entries.nextElement();
		
		File f = new File("plugin:/" + fPluginNS + "/" + root.getPath());
		SVDBFile pp_file = findPreProcFile(f);
		
		if (pp_file == null) {
			System.out.println("Failed to find file \"" + f.getPath() + "\"");
		}
		SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
		
		prepareFileTree(ft_root, null);
		processFile(ft_root, dp);
		
		fFileIndexValid = true;
		long end = System.currentTimeMillis();
		System.out.println("<-- buildIndex(" + (end-start) + ")");
	}
	
	@SuppressWarnings("unchecked")
	private void processFile(
			SVDBFileTree 				path,
			SVPreProcDefineProvider		dp) {
		dp.setFileContext(path);
		
		SVDBFileFactory scanner = new SVDBFileFactory(dp);
		
		String path_s = path.getFilePath().getPath();
		
		path_s = path_s.substring("plugin:/".length());
		if (path_s.indexOf('/') == -1) {
			System.out.println("[ERROR] problem parsing lib-index file \"" + 
					path.getFilePath().getPath() + "\"");
			return;
		}
		path_s = path_s.substring(path_s.indexOf('/'));
		
		File path_f = new File(path_s);

		Enumeration<URL> entries = (Enumeration<URL>)fBundle.findEntries(
				path_f.getParent(), path_f.getName(), false);
		
		try {
			URL url = entries.nextElement();
			InputStream in = url.openStream();
			BufferedInputStream in_b = new BufferedInputStream(in);
			
			SVDBFile svdb_f = scanner.parse(in_b, path.getFilePath().getPath());

			System.out.println("Add path \"" + path.getFilePath().getPath() + 
					"\" to index");
			fFileIndex.put(path.getFilePath(), svdb_f);
		} catch (IOException e) {
			e.printStackTrace();
		}

		// Now, recurse through the files included
		for (SVDBFileTree ft_t : path.getIncludedFiles()) {
			System.out.println("included file \"" + ft_t.getFilePath().getPath() + "\"");
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
			System.out.println("it=" + it.getName());
			if (it.getType() == SVDBItemType.Include) {
				System.out.println("include file: " + it.getName());
				SVDBFile f = new SVDBIncludeSearch(this).findIncludedFile(it.getName());

				SVDBFileTree ft = new SVDBFileTree((SVDBFile)f.duplicate());
				root.getIncludedFiles().add(ft);
				
				prepareFileTree(ft, root);
			} else if (it instanceof SVDBScopeItem) {
				System.out.println("scope: " + it);
				addIncludeFiles(root, (SVDBScopeItem)it);
			}
		}
	}
}
