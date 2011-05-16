package net.sf.sveditor.ui;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

public class RefreshIndexJob extends Job {
	private List<ISVDBIndex>			fIndexRebuildList;
	private SVUiPlugin					fParent;
	
	public RefreshIndexJob(SVUiPlugin parent) {
		super("Refresh Index");
		fIndexRebuildList = new ArrayList<ISVDBIndex>();
		fParent = parent;
	}
	
	public void addIndex(ISVDBIndex index) {
		synchronized (fIndexRebuildList) {
			fIndexRebuildList.add(index);
		}
	}
	
	public void addIndexList(List<ISVDBIndex> list) {
		synchronized (fIndexRebuildList) {
			fIndexRebuildList.addAll(list);
		}
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		synchronized (fIndexRebuildList) {
			monitor.beginTask("Refreshing Indexes", fIndexRebuildList.size());
		}
		
		while (true) {
			ISVDBIndex index = null;
			synchronized (fIndexRebuildList) {
				if (fIndexRebuildList.size() == 0) {
					break;
				} else {
					index = fIndexRebuildList.remove(0);
				}
			}
			
			SubProgressMonitor sub = new SubProgressMonitor(monitor, 1);
			index.loadIndex(sub);
		}
		monitor.done();
		fParent.refreshJobComplete();
		
		return Status.OK_STATUS;
	}

}
