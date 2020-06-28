/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.ui.svcp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexChangeListener;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexChangeEvent;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.search.SVDBSearchResult;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;

public class SVDBFileErrorDecorator 
		implements ILightweightLabelDecorator, IResourceChangeListener {
	private List<ILabelProviderListener>					fListeners;
	private Thread											fLookupThread;
	private Map<String, Map<String, Boolean>>				fManagedByIndex;
	private Map<SVDBIndexCollection, IndexChangeListener>	fProjectListeners;
	private WeakHashMap<Object, Object>						fManagedObjects;
	private List<Object>									fWorkQueue;
	
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
				
				if (work instanceof IFile) {
					IFile elem = (IFile)work;
					// Elem not null
					IProject p = elem.getProject();
					String pname = p.getName();
					SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
					SVDBProjectData pdata = pmgr.getProjectData(p);
					SVDBIndexCollection index = pdata.getProjectIndexMgr();
					
					String path = "${workspace_loc}" + elem.getFullPath().toOSString();
					
					path = SVFileUtils.normalize(path);

					List<SVDBSearchResult<SVDBFile>> res = index.findFile(path, false); 
							

					synchronized (fManagedByIndex) {
						Map<String, Boolean> proj_map = fManagedByIndex.get(p.getName());
						if (proj_map == null) {
							proj_map = new HashMap<String, Boolean>();
							fManagedByIndex.put(p.getName(), proj_map);
							if (!fProjectListeners.containsKey(index)) {
								IndexChangeListener l = new IndexChangeListener(pname);
								fProjectListeners.put(index, l);
								index.addIndexChangeListener(l);
							}
						}
						proj_map.remove(elem);
						proj_map.put(elem.getFullPath().toOSString(), 
								(res != null && res.size() > 0));
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
		}
	};
	
	private Runnable fireChangeRunnable = new Runnable() {
		
		public void run() {
			LabelProviderChangedEvent ev = new LabelProviderChangedEvent(SVDBFileErrorDecorator.this);
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

		
		@Override
		public void index_event(SVDBIndexChangeEvent e) {
			queueWork(this);
		}

	};
	
	public SVDBFileErrorDecorator() {
		fListeners = new ArrayList<ILabelProviderListener>();
		fWorkQueue = new ArrayList<Object>();
		fManagedByIndex = new HashMap<String, Map<String,Boolean>>();
		fProjectListeners = new WeakHashMap<SVDBIndexCollection, SVDBFileErrorDecorator.IndexChangeListener>();
		fManagedObjects = new WeakHashMap<Object, Object>();
	
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
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
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
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
	
	public void resourceChanged(IResourceChangeEvent event) {
		
	}

	public void decorate(Object element, IDecoration decoration) {
		IWorkbench workbench = PlatformUI.getWorkbench();
		
		if (workbench.isClosing()) {
			return;
		}

		if (element instanceof IResource) {
			if (!((IResource)element).isAccessible()) {
				return;
			}
		}
		
		if (element instanceof IFile) {
			IFile file = (IFile)element;
			String path = ((IFile)element).getFullPath().toOSString();
			
			synchronized (fManagedByIndex) {
				Map<String, Boolean> proj_map = fManagedByIndex.get(file.getProject().getName());
				if (proj_map == null || !proj_map.containsKey(path)) {
					SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
					SVDBProjectData pdata = pmgr.getProjectData(file.getProject());
					SVDBIndexCollection index = pdata.getProjectIndexMgr();
					String pname = file.getProject().getName();
				
					if (index.isFileListLoaded()) {
						if (proj_map == null) {
							proj_map = new HashMap<String, Boolean>();
							fManagedByIndex.put(pname, proj_map);
							if (fProjectListeners.containsKey(index)) {
								IndexChangeListener l = new IndexChangeListener(pname);
								fProjectListeners.put(index, l);
								index.addIndexChangeListener(l);
							}
						}
						List<SVDBSearchResult<SVDBFile>> res = index.findFile("${workspace_loc}" + path, false);
						proj_map.put(path, (res != null && res.size() > 0));
					} else {
						// Queue a job to do the same thing...
						queueWork(element);
					}
				}
			}
		}
		
		IResource res = (IResource) element;
		try {
			if (res.findMaxProblemSeverity(IMarker.PROBLEM, true, IResource.DEPTH_INFINITE) >= IMarker.SEVERITY_ERROR) {
				ImageDescriptor image = SVUiPlugin.getImageDescriptor(
						"/icons/ovr16/error_co.gif");
				if (image != null) {
					decoration.addOverlay(image);
				}
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}
}
