package net.sf.sveditor.core.db.index;

import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBIndexCollectionMgr {
	
	private List<Reference<SVDBIndexCollection>>			fIndexCollectionList;
	private boolean										fCreateShadowIndexes;
	
	public SVDBIndexCollectionMgr() {
		fIndexCollectionList = new ArrayList<Reference<SVDBIndexCollection>>();
	}
	
	public void addIndexCollection(SVDBIndexCollection c) {
		fIndexCollectionList.add(new WeakReference<SVDBIndexCollection>(c));
		// TODO: fire creation listeners (?)
	}
	
	public void setCreateShadowIndexes(boolean create) {
		boolean fire = (fCreateShadowIndexes != create);
		
		if (fire) {
			for (int i=0; i<fIndexCollectionList.size(); i++) {
				if (fIndexCollectionList.get(i).get() != null) {
					fIndexCollectionList.get(i).get().settingsChanged();
				} else {
					fIndexCollectionList.remove(i);
					i--;
				}
			}
		}
		
		fCreateShadowIndexes = create;
	}
	
	public boolean getCreateShadowIndexes() {
		return fCreateShadowIndexes;
	}
	
	public void loadIndex(IProgressMonitor monitor) {
		SubProgressMonitor sm = new SubProgressMonitor(monitor, 1);
		
		synchronized (fIndexCollectionList) {
			sm.beginTask("loadIndex", fIndexCollectionList.size());
			for (int i=0; i<fIndexCollectionList.size(); i++) {
				if (fIndexCollectionList.get(i).get() == null) {
					fIndexCollectionList.remove(i);
					i--;
				} else {
					fIndexCollectionList.get(i).get().loadIndex(
							new SubProgressMonitor(sm, 1));
				}
			}
		}
		
		sm.done();
	}

}
