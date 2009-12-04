package net.sf.sveditor.core.db.index.src_collection;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBPreProcObserver;
import net.sf.sveditor.core.db.index.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIncludeFileProvider;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.search.SVDBSearchResult;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

/* 
 * Manages the index for a workspace location
 * 
 */
public class SVDBSourceCollectionIndex 
	extends AbstractSVDBIndex implements ISVDBIncludeFileProvider {
	
	protected int								fIndexType;

	protected String							fBaseLocation;
	protected boolean							fDisposed;

	protected List<ISVDBIndexChangeListener>	fIndexChageListeners;
	
	protected List<ISVDBIncludeFileProvider>	fIncludePaths;
	
	protected SVDBFileTreeUtils					fFileTreeUtils;
	protected AbstractSVFileMatcher				fFileMatcher;
	
	public SVDBSourceCollectionIndex(
			String					project,
			String 					base_location,
			int						index_type,
			AbstractSVFileMatcher	file_matcher,
			ISVDBFileSystemProvider	fs_provider) {
		super(project, fs_provider);

		fFileMatcher = file_matcher;
		
		if (fFileMatcher == null) {
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		fBaseLocation = base_location;
		fIndexType    = index_type;
		fIndexChageListeners = new ArrayList<ISVDBIndexChangeListener>();

		fFileTreeUtils    = new SVDBFileTreeUtils();
	}
	
	public String getTypeID() {
		return SVDBSourceCollectionIndexFactory.TYPE;
	}

	@Override
	protected boolean isLoadUpToDate() {
		List<String> files = fFileMatcher.findIncludedPaths();
		
		if (files.size() != fFileList.size()) {
			System.out.println("    Index not up-to-date: files.size=" + 
					files.size() + " fFileList.size=" + fFileList.size());
			return false;
		}
		
		for (String file : files) {
			SVDBFile pp_file = fFileList.get(file);
			
			if (pp_file == null ||
					(pp_file.getLastModified() != fFileSystemProvider.getLastModifiedTime(file))) {
				if (pp_file == null) {
					System.out.println("    Index not up-to-date: file \"" +
							file + "\" not in index");
				} else {
					System.out.println("    Index not up-to-date: file \"" +
							file + "\" cached timestamp " + pp_file.getLastModified() + 
							" filesystem timestamp " + fFileSystemProvider.getLastModifiedTime(file));
				}
				return false;
			}
		}
		
		return true;
	}

	public void dispose() {
		super.dispose();
		fDisposed = true;
	}
	
	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		
		if (!fDisposed) {
			dispose();
		}
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public SVDBFile parse(InputStream in, String path) {
		SVDBFileTreeUtils utils = new SVDBFileTreeUtils();

		Map<String, SVDBFile> pp_map = getPreProcFileMap();
		
		SVDBFileTree ft = utils.createFileContext(pp_map.get(path), this);
		
		return parseFile(in, path, ft);
	}
	
	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		
		Iterator<String> it = map.keySet().iterator();
		
		while (it.hasNext()) {
			String f = it.next();
			
			String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
			
			if (norm_path.endsWith(leaf)) {
				return new SVDBSearchResult<SVDBFile>(map.get(f), this);
			}
		}
		
		return null;
	}
	
	protected synchronized void buildPreProcFileMap() {
		try {
			SVPreProcScanner sc            = new SVPreProcScanner();
			SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
		
			sc.setObserver(s_observer);

			// 	Discover files
			System.out.println("Building SourceCollection index " + fBaseLocation);
			if (fFileMatcher == null) {
				try {
					throw new Exception();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
			for (String path : fFileMatcher.findIncludedPaths()) {
				System.out.println("    path=" + path);
				if (fFileList.containsKey(path)) {
					fFileList.remove(path);
				}
				fFileList.put(path, createPreProcFile(path));
			}
		} catch (Exception e) { 
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileListValid = true;
			}
		}
	}
	
	private SVDBFile createPreProcFile(String file) {
		SVPreProcScanner sc            = new SVPreProcScanner();
		SVDBPreProcObserver s_observer = new SVDBPreProcObserver();
	
		sc.setObserver(s_observer);

		try {
			InputStream in = fFileSystemProvider.openStream(file);
			sc.init(in, file);
			sc.scan();
			
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

		if (s_observer.getFiles().size() > 0) {
			SVDBFile svdb_f = s_observer.getFiles().get(0);
			
			svdb_f.setLastModified(fFileSystemProvider.getLastModifiedTime(file));
			
			return svdb_f;
		} else {
			return null;
		}
	}
	
	protected synchronized void buildIndex() {
		System.out.println("SourceCollectionIndex: updateFileIndex \"" + fBaseLocation + "\"");
		
		try {
			Map<String, SVDBFile> pp_file_map = getPreProcFileMap();

			Iterator<String> it = pp_file_map.keySet().iterator();

			while (it.hasNext()) {
				String file = it.next();
				System.out.println("    file=" + file);
				
				if (!fFileIndex.containsKey(file)) {
					SVDBFileTree ft = fFileTreeUtils.createFileContext(
							pp_file_map.get(file), this);
					SVDBFile svdb_file = parseFile(file, ft);
					
					synchronized(fFileIndex) {
						fFileIndex.put(file, svdb_file);
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			synchronized (this) {
				fFileIndexValid = true;
			}
		}
	}
	
	private SVDBFile parseFile(String file, SVDBFileTree file_tree) {
		InputStream in = fFileSystemProvider.openStream(file);
		return parseFile(in, file, file_tree);
	}

	private SVDBFile parseFile(InputStream in, String path, SVDBFileTree file_tree) {
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();
		SVDBFile svdb_file = null;
		
		System.out.println("file_tree=" + file_tree);

		// Where do defines come from?
		dp.setFileContext(file_tree);
		
		svdb_file = SVDBFileFactory.createFile(in, path, dp);
		
		svdb_file.setLastModified(fFileSystemProvider.getLastModifiedTime(path));

		try {
			in.close();
		} catch (IOException e) { }
		
		return svdb_file;
	}

	/*
	public SVDBFile findIncludedFile(String leaf) {
		System.out.println("findIncludedFile: " + leaf);
		
		Iterator<String> it = getPreProcFileMap().keySet().iterator();
		
		while (it.hasNext()) {
			String file = it.next();
			
			// Normalize the path so this works on Windows
			String path_norm =
				fWinPathPattern.matcher(file).replaceAll("/");
			
			if (path_norm.endsWith(leaf)) {
				// TODO: opportunity for caching
				return getPreProcFileMap().get(file);
			}
		}
		
		if (fIncludeProvider != null) {
			return fIncludeProvider.findIncludedFile(leaf);
		} else {
			System.out.println("[ERROR] SourceCollectionIndex @ " +
					fBaseLocation + " does not have IncludeProvider");
		}
		
		return null;
	}
	 */

	public int getIndexType() {
		return fIndexType;
	}

	public void rebuildIndex() {
		// TODO: force index and map to be invalid
		System.out.println("[TODO] SVDBIndexBase.rebuildIndex");
	}
	
	public void addChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.add(l);
	}

	public void removeChangeListener(ISVDBIndexChangeListener l) {
		fIndexChageListeners.remove(l);
	}

	protected void fileRemoved(String file) {
		fFileList.remove(file);
		SVDBFile svdb_file = fFileIndex.remove(file);

		if (svdb_file != null) {
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_REMOVED, svdb_file);
			}
		}
	}
	
	protected void fileAdded(String file) {
		// First, decide whether this is a file to ignore
		if (file.lastIndexOf('.') != -1) {
			String ext = file.substring(file.lastIndexOf('.'));
			
			if (!fSVExtensions.contains(ext)) {
				return;
			}
			
			// Next, check whether there is an ignore dir on the path
			File parent = new File(file).getParentFile();
			File last_parent = null;
			
			while (parent != null &&
					(last_parent == null || !last_parent.equals(parent))) {
				if (fIgnoreDirs.contains(parent.getName())) {
					return;
				}
				last_parent = parent;
				parent = parent.getParentFile();
			}
		} else {
			return;
		}
		
		if (fFileListValid) {
			if (fFileList.containsKey(file)) {
				// hmmm... bad information
				fFileList.remove(file);
			}
			
			fFileList.put(file, createPreProcFile(file));
		}
		
		if (fFileIndexValid) {
			Map<String, SVDBFile> pp_file_map = getPreProcFileMap();
			
			if (fFileIndex.containsKey(file)) {
				fFileIndex.remove(file);
			}
			
			SVDBFileTree ft = fFileTreeUtils.createFileContext(
					pp_file_map.get(file), this);
			SVDBFile svdb_file = parseFile(file, ft);
			
			synchronized(fFileIndex) {
				fFileIndex.put(file, svdb_file);
			}
			
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_ADDED, svdb_file);
			}
		}
	}
	
	
	protected void fileChanged(String file) {
		
		if (fFileList.containsKey(file)) {
			fFileList.remove(file);
			fFileList.put(file, createPreProcFile(file));
		}

		if (fFileIndex.containsKey(file)) {
			Map<String, SVDBFile> pp_file_map = getPreProcFileMap();
			
			SVDBFileTree ft = fFileTreeUtils.createFileContext(
					pp_file_map.get(file), this);
			SVDBFile svdb_file = parseFile(file, ft);
			SVDBFile svdb_file_e = fFileIndex.get(file);

			// Merge any new content with the existing
			SVDBFileMerger.merge(svdb_file_e, svdb_file, null, null, null);
			
			for (ISVDBIndexChangeListener l : fIndexChageListeners) {
				l.index_changed(ISVDBIndexChangeListener.FILE_CHANGED, svdb_file_e);
			}
		}
	}
}
