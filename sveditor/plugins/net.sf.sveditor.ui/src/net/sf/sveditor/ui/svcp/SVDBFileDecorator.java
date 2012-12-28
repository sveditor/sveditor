package net.sf.sveditor.ui.svcp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.widgets.Display;

public class SVDBFileDecorator implements ILightweightLabelDecorator {
	private List<ILabelProviderListener>		fListeners;
	private Thread								fLookupThread;
	private Map<String, Set<String>>			fManagedByIndex;
	private Map<SVDBIndexCollection, IndexChangeListener>	fProjectListeners;
	private List<Object>						fWorkQueue;
	
	private Runnable lookupRunnable = new Runnable() {
		
		public void run() {
			while (true) {
				Object work = null;
				
				synchronized (fWorkQueue) {
					for (int i=0; i<2; i++) {
						if (fWorkQueue.size() > 0) {
							work = fWorkQueue.remove(0);
						} else if (i == 0) {
							try {
								fWorkQueue.wait(5);
							} catch (InterruptedException e) {}
						}
					}
					
					if (work == null) {
						fLookupThread = null;
						break;
					}
				}
				
				if (work instanceof IResource) {
					IResource elem = (IResource)work;
					// Elem not null
					IProject p = elem.getProject();
					String pname = p.getName();
					SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
					SVDBProjectData pdata = pmgr.getProjectData(p);
					SVDBIndexCollection index = pdata.getProjectIndexMgr();
					
					String path = "${workspace_loc}" + elem.getFullPath().toOSString();
					
					path = SVFileUtils.normalize(path);

					synchronized (fManagedByIndex) {
						Set<String> proj_map = fManagedByIndex.get(p.getName());
						if (proj_map == null) {
							proj_map = new HashSet<String>();
							fManagedByIndex.put(p.getName(), proj_map);
							if (!fProjectListeners.containsKey(index)) {
								IndexChangeListener l = new IndexChangeListener(pname);
								fProjectListeners.put(index, l);
								index.addIndexChangeListener(l);
							}
							loadProjectFiles(proj_map, index);
						}
					}
				} else if (work instanceof IndexChangeListener) {
					IndexChangeListener l = (IndexChangeListener)work;
					String project = l.getProject();
					
					synchronized (fManagedByIndex) {
						fManagedByIndex.remove(project);
					}
				}
			}
			
			Display.getDefault().asyncExec(fireChangeRunnable);
			/**
			// We're done
			synchronized (this) {
				if (!fFireChangeRunnableQueued) {
					fFireChangeRunnableQueued = true;
				}
			}
			 */
		}
	};
	
	private Runnable fireChangeRunnable = new Runnable() {
		
		public void run() {
			LabelProviderChangedEvent ev = new LabelProviderChangedEvent(SVDBFileDecorator.this);
			for (ILabelProviderListener l : fListeners) {
				l.labelProviderChanged(ev);
			}
		}
	};
	
	private class IndexChangeListener implements ISVDBIndexChangeListener {
		private String				fProject;
		
		public IndexChangeListener(String project) {
			fProject = project;
		}
		
		public String getProject() {
			return fProject;
		}

		public void index_changed(int reason, SVDBFile file) {
			switch (reason) {
				case FILE_ADDED:
				case FILE_REMOVED:
					queueWork(this);
					break;
			}
		}

		public void index_rebuilt() {
			queueWork(this);
		}
	};
	
	public SVDBFileDecorator() {
		fListeners = new ArrayList<ILabelProviderListener>();
		fWorkQueue = new ArrayList<Object>();
		fManagedByIndex = new HashMap<String, Set<String>>();
		fProjectListeners = new WeakHashMap<SVDBIndexCollection, SVDBFileDecorator.IndexChangeListener>();
	}

	public void addListener(ILabelProviderListener listener) {
		synchronized (fListeners) {
			fListeners.add(listener);
		}
	}
	
	public void removeListener(ILabelProviderListener listener) {
		synchronized (fListeners) {
			fListeners.remove(listener);
		}
	}

	public void dispose() {
		synchronized (fListeners) {
			fListeners.clear();
		}
	}

	public boolean isLabelProperty(Object element, String property) {
		// TODO Auto-generated method stub
		return false;
	}
	
	private void queueWork(Object work) {
		synchronized (fWorkQueue) {
			if (!fWorkQueue.contains(work)) {
				fWorkQueue.add(work);
				if (fLookupThread == null) {
					fLookupThread = new Thread(lookupRunnable);
					fLookupThread.start();
				}
				fWorkQueue.notifyAll();
			}
		}
	}

	public void decorate(Object element, IDecoration decoration) {
		ImageDescriptor image = null;
		
		if (element instanceof IResource) {
			IResource rsrc = (IResource)element;
			String path = "${workspace_loc}" + rsrc.getFullPath().toOSString();
			String project_name = rsrc.getProject().getName();
			
			path = SVFileUtils.normalize(path);
			
			synchronized (fManagedByIndex) {
				Set<String> proj_map = fManagedByIndex.get(project_name);
				if (proj_map != null && proj_map.contains(path)) {
					image = SVUiPlugin.getImageDescriptor(
							"/icons/ovr16/indexed_6x6.gif");
					if (image != null) {
						decoration.addOverlay(image);
					}
				} else {
					SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
					SVDBProjectData pdata = pmgr.getProjectData(rsrc.getProject());
					SVDBIndexCollection index = pdata.getProjectIndexMgr();
				
					if (index.isFileListLoaded()) {
						if (proj_map == null) {
							proj_map = new HashSet<String>();
							fManagedByIndex.put(project_name, proj_map);
							if (!fProjectListeners.containsKey(index)) {
								IndexChangeListener l = new IndexChangeListener(project_name);
								fProjectListeners.put(index, l);
								index.addIndexChangeListener(l);
							}
							loadProjectFiles(proj_map, index);
						}
						
						if (proj_map.contains(path)) {
							image = SVUiPlugin.getImageDescriptor(
									"/icons/ovr16/indexed_6x6.gif");
							if (image != null) {
								decoration.addOverlay(image);
							}	
						}
					} else {
						// Queue a job to do the same thing...
						queueWork(element);
					}
				}
			}
		}
	}
	
	private void loadProjectFiles(Set<String> proj_map, SVDBIndexCollection index) {
		Iterable<String> file_list = index.getFileList(new NullProgressMonitor());
	
		for (String path : file_list) {
			// Add all paths and directories in this index collection
			if (path.startsWith("${workspace_loc}")) {
				if (!proj_map.contains(path)) {
					proj_map.add(path);
				}


				// Add directories
				int start_idx = path.indexOf('/');

				if (start_idx != -1) {
					start_idx++;
					int end_idx = start_idx;
					while ((end_idx = path.indexOf('/', end_idx)) != -1) {
						String path_seg = path.substring(0, end_idx);

						if (!proj_map.contains(path_seg)) {
							proj_map.add(path_seg);
						}

						end_idx++;
					}
				}
			}
		}
	}
}
