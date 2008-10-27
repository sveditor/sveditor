package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.internal.resources.WorkspaceRoot;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

/**
 * Manager for SVDBFile objects. Caches a collection of active 
 * files. This object is effectively a singleton in practice.
 * <br>
 * <br>
 * The SVDBFileManager provides notification to listeners when an active
 * file changes, and listens to Eclipse resource events.
 * <br>
 * <br>
 * 
 * TODO: need to use an Eclipse job to decouple parsing from event notification.
 * 
 * @author ballance
 *
 */
public class SVDBFileManager 
	implements IResourceChangeListener, IResourceDeltaVisitor {
	
	private List<ISVDBChangeListener>				fListeners;
	private WeakHashMap<File, SVDBFile>				fFileCache;
	private Map<File, SVDBFile>						fBackupCache;
	private IWorkspace								fWS;
	
	
	public SVDBFileManager() {
		fListeners   = new ArrayList<ISVDBChangeListener>();
		fFileCache   = new WeakHashMap<File, SVDBFile>();
		fBackupCache = new HashMap<File, SVDBFile>();
		fWS = ResourcesPlugin.getWorkspace(); 
		
		fWS.addResourceChangeListener(this);
	}
	
	public void addSVDBChangeListener(ISVDBChangeListener l) {
		fListeners.add(l);
	}
	
	public void removeSVDBChangeListener(ISVDBChangeListener l) {
		fListeners.remove(l);
	}
	
	public void dispose() {
		fWS.removeResourceChangeListener(this);
	}
	
	public void setLiveSource(File file, SVDBFile in) {
		List<SVDBItem> adds = new ArrayList<SVDBItem>();
		List<SVDBItem> rem  = new ArrayList<SVDBItem>();
		List<SVDBItem> chg  = new ArrayList<SVDBItem>();
		
		ISVDBFileProvider file_p = null;
		
		IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot(); 
		IFile ifile = ws_root.getFileForLocation(new Path(file.getAbsolutePath()));
		
		if (ifile != null) {
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
			IProject proj = ifile.getProject();
			SVDBProjectData pdata = mgr.getProjectData(proj);
			
			file_p = new SVDBProjectDataFileProvider(pdata);
		}
		
		if (!fFileCache.containsKey(file) || !fBackupCache.containsKey(file)) {
			if (!fFileCache.containsKey(file)) {
				SVDBFile f = parseFile(file, file_p);
				fFileCache.put(file, f);
			}
			
			SVDBFile fs_file = (SVDBFile)fFileCache.get(file).duplicate();
			fBackupCache.put(file, fs_file);
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
	
	private static SVDBFile parseFile(File f, ISVDBFileProvider file_provider) {
		SVDBFile    file = null;
		InputStream in   = null;
		
		try {
			in = new FileInputStream(f);
			file = SVDBFileFactory.createFile(
					in, f.getAbsolutePath(), file_provider);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return file;
	}

}
