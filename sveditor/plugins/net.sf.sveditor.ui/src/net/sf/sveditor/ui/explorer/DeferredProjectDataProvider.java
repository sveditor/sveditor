package net.sf.sveditor.ui.explorer;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.widgets.Display;

public abstract class DeferredProjectDataProvider implements IProjectPathsData {
	private IProjectPathsData			fParent;
	private String						fName;
	private Object						fWorkLock = new Object();
	private boolean						fWaiting;
	private Object						fChildren[];
	private Job							fWorkJob;
	private long						fWaitInt = 1;
	
	public DeferredProjectDataProvider(IProjectPathsData p, String name) {
		fParent = p;
		fName = name;
	}

	@Override
	public String getName() {
		return fName;
	}

	@Override
	public Object getParent(Object element) {
		return fParent;
	}
	
	public void reset() {
		synchronized (fWorkLock) {
			fChildren = null;
		}
	}
	
	public abstract Object[] getChildrenDeferred(Object parent);

	@Override
	public Object[] getChildren(final Object parent) {
		synchronized (fWorkLock) {
			if (fChildren != null) {
				Object ret[] = fChildren;
//				fChildren = null;
				return ret;
			}
			
			if (fWorkJob == null) {
				fWorkJob = new Job("Fetch " + fName) {
					
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						Object c[] = getChildrenDeferred(parent);
						
						synchronized (fWorkLock) {
							fChildren = c;
							if (fWaiting) {
								fWorkLock.notify();
							} else {
								IProjectPathsData p = (IProjectPathsData)parent;
								while (p.getParent(p) != null) {
									p = (IProjectPathsData)p.getParent(p);
								}
								final ProjectPathsData pp = (ProjectPathsData)p;
								Display.getDefault().asyncExec(new Runnable() {
									public void run() { 
										pp.getViewer().refresh(
												DeferredProjectDataProvider.this, true);
									}
								});
							}
							fWorkJob = null;
						}
						return Status.OK_STATUS;
					}
				};				
				fWorkJob.schedule();
	
				// See if the job finishes quickly
				fWaiting = true;
				try {
					fWorkLock.wait(fWaitInt);
				} catch (InterruptedException e) { }
				fWaiting = false;
			
				// Call to see if we've received the answer
				return getChildren(parent);
			}
		}
	
		return new Object[0];
	}

	@Override
	public boolean hasChildren() {
		return true;
	}

}
