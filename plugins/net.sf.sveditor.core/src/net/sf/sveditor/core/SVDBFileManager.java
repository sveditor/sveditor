package net.sf.sveditor.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

public class SVDBFileManager 
	implements IResourceChangeListener, IResourceDeltaVisitor {
	private List<ISVDBChangeListener>				fListeners;
	private WeakHashMap<File, SVDBFile>				fFileCache;
	private WeakHashMap<File, SVDBFile>				fLiveSourceCache;
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
		
		if (!fFileCache.containsKey(file) || !fBackupCache.containsKey(file)) {
			if (!fFileCache.containsKey(file)) {
				SVDBFile f = parseFile(file);
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

	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getDelta() == null) {
			return;
		}

		try {
			event.getDelta().accept(this);
		} catch (CoreException e) {}
	}

	@Override
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
		
		SVDBFile new_file = parseFile(file);
		
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
		SVDBFile ret = null;
		
		if (fFileCache.containsKey(f)) {
			ret = fFileCache.get(f);
		}
		
		if (ret == null) {
			ret = parseFile(f);
			fFileCache.put(f, ret);
		}
		
		return ret;
	}
	
	public static SVDBFile parseFile(File f) {
		SVDBFile    file = null;
		InputStream in   = null;
		
		try {
			in = new FileInputStream(f);
			file = SVDBFileFactory.createFile(in, f.getAbsolutePath());
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return file;
	}

}
