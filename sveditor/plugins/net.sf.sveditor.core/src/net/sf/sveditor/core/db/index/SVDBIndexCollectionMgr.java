package net.sf.sveditor.core.db.index;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

public class SVDBIndexCollectionMgr {
	
	private List<WeakReference<SVDBIndexCollection>>			fIndexCollectionList;
	private boolean											fCreateShadowIndexes;
	
	public SVDBIndexCollectionMgr() {
		fIndexCollectionList = new ArrayList<WeakReference<SVDBIndexCollection>>();
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
	

}
