package net.sf.sveditor.core;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;

/**
 * Manager for SVDBFile objects. Caches a collection of active 
 * files. This object is effectively a singleton in practice.
 * <br>
 * <br>
 * The SVDBWorkspaceFileManager provides notification to listeners when an active
 * file changes, and listens to Eclipse resource events.
 * <br>
 * <br>
 * 
 * TODO: need to use an Eclipse job to decouple parsing from event notification.
 * 
 * TODO: may wish to thin this class down a bit. Some of the functionality 
 *       is a duplicate of what is already in the SVDBIndex classes
 * 
 * @author ballance
 *
 */
public class SVDBWorkspaceFileManager 
	/* implements IResourceChangeListener, IResourceDeltaVisitor  */{
	
	private List<ISVDBChangeListener>				fListeners;
	private WeakHashMap<File, SVDBFile>				fFileCache;
	private Map<File, SVDBFile>						fBackupCache;
	
	
	public SVDBWorkspaceFileManager() {
		fListeners   = new ArrayList<ISVDBChangeListener>();
		fFileCache   = new WeakHashMap<File, SVDBFile>();
		fBackupCache = new HashMap<File, SVDBFile>();
		
		/*
		fWS = ResourcesPlugin.getWorkspace(); 
		fWS.addResourceChangeListener(this);
		 */
	}
	
	public void addSVDBChangeListener(ISVDBChangeListener l) {
		fListeners.add(l);
	}
	
	public void removeSVDBChangeListener(ISVDBChangeListener l) {
		fListeners.remove(l);
	}
	
	public void dispose() {
		// fWS.removeResourceChangeListener(this);
	}
	
	/*
	public void setLiveSource(IFile ifile, SVDBFile in) {
		List<SVDBItem> adds = new ArrayList<SVDBItem>();
		List<SVDBItem> rem  = new ArrayList<SVDBItem>();
		List<SVDBItem> chg  = new ArrayList<SVDBItem>();
		File file = ifile.getLocation().toFile();
		
		if (!fFileCache.containsKey(file)) {
			if (!fFileCache.containsKey(file)) {
				SVDBFile f = getFile(ifile);
				fFileCache.put(file, f);
			}
			
			SVDBFile fs_file = (SVDBFile)fFileCache.get(file);
			
			if (fs_file != null) {
				fs_file = (SVDBFile)fs_file.duplicate();
				fBackupCache.put(file, fs_file);
			} else {
				System.out.println("Failed to get \"" + file + "\"");
				return;
			}
		}
		
		SVDBFile pub_file = fFileCache.get(file);
		SVDBFileMerger.merge(pub_file, in, adds, rem, chg);
		
		for (ISVDBChangeListener l : fListeners) {
			l.SVDBFileChanged(pub_file, adds, rem, chg);
		}
	}
	
	public void removeLiveSource(File file) {
		List<SVDBItem> adds = new ArrayList<SVDBItem>();
		List<SVDBItem> rem  = new ArrayList<SVDBItem>();
		List<SVDBItem> chg  = new ArrayList<SVDBItem>();

		if (fBackupCache.containsKey(file)) {
			SVDBFile bak_file = fBackupCache.get(file);
			SVDBFile pub_file = fFileCache.get(file);
			
			SVDBFileMerger.merge(pub_file, bak_file, adds, rem, chg);

			fBackupCache.remove(file);
			
			for (ISVDBChangeListener l : fListeners) {
				l.SVDBFileChanged(pub_file, adds, rem, chg);
			}
		}
	}
	 */

	/*
	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getDelta() == null) {
			return;
		}

		try {
			event.getDelta().accept(this);
		} catch (CoreException e) {}
	}

	
	public boolean visit(IResourceDelta delta) throws CoreException {
		File                file      = delta.getResource().getLocation().toFile();
		SVDBFile            svdb_file = null;
		List<SVDBItem>		adds      = new ArrayList<SVDBItem>();
		List<SVDBItem>		removes   = new ArrayList<SVDBItem>();
		List<SVDBItem>		changes   = new ArrayList<SVDBItem>();
		
		if (!file.isFile()) {
			return true;
		}
		
		if (fFileCache.containsKey(file)) {
			svdb_file = fFileCache.get(file);
		}
		
		SVDBProjectManager pmgr  = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData    pdata = pmgr.getProjectData(
				delta.getResource().getProject()); 
		
		ISVDBFileProvider file_p = null;
		
		if (pdata != null) {
			file_p = new SVDBProjectDataFileProvider(pdata);
		}
		SVDBFile new_file = parseFile(file, file_p);
		
		if (svdb_file != null) {
			SVDBFileMerger.merge(svdb_file, new_file,
					adds, removes, changes);
			for (ISVDBChangeListener l : fListeners) {
				l.SVDBFileChanged(svdb_file, adds, removes, changes);
			}
		}

		return true;
	}
	
	public SVDBFile getFile(File f) {
		System.out.println("[FIXME] getFile(null)");
		return getFile(f, null);
	}
	
	
	public SVDBFile getFile(File f, ISVDBFileProvider file_provider) {
		SVDBFile ret = null;
		
		if (fFileCache.containsKey(f)) {
			ret = fFileCache.get(f);
		}
		
		if (ret == null) {
			ret = parseFile(f, file_provider);
			fFileCache.put(f, ret);
		}
		
		return ret;
	}
	 */
	
	/**
	 * 
	 * Used only by SV ContentProvider 
	 * @param f
	 * @return
	 */
	public SVDBFile getFile(IFile f) {
		IProject           p   = f.getProject();
		SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = mgr.getProjectData(p);
		
		if (pd != null) {
			File file = f.getLocation().toFile();
			if (fFileCache.containsKey(file)) {
				return fFileCache.get(file);
			} else {
				// TODO: Want to do something far simpler. Just scan the file
				// (without expanding macros)
				// return pd.getFileIndex().findFile(f.getLocation().toFile());
			}
		} else {
			System.out.println("[ERROR] failed to locate project data for \"" + 
					f.getLocation() + "\"");
		}
			
		return null;
	}
	
	/*
	private static SVDBFile parseFile(File f, ISVDBFileProvider file_provider) {
		SVDBFile    file = null;
		InputStream in   = null;
		
		System.out.println("[FIXME] SVDBWorkspaceFileManager.parseFile()");
		
		try {
			in = new FileInputStream(f);
			file = SVDBFileFactory.createFile(
					in, f.getAbsolutePath(), file_provider);
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return file;
	}
	 */

}
