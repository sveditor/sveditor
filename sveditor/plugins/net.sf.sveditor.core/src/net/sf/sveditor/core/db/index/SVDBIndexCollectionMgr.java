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
package net.sf.sveditor.core.db.index;

import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

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
		SubMonitor subMonitor = SubMonitor.convert(monitor);
		
		synchronized (fIndexCollectionList) {
			subMonitor.setTaskName("Load Index");
			subMonitor.setWorkRemaining(fIndexCollectionList.size());
			for (int i=0; i<fIndexCollectionList.size(); i++) {
				if (fIndexCollectionList.get(i).get() == null) {
					fIndexCollectionList.remove(i);
					i--;
				} else {
					fIndexCollectionList.get(i).get().loadIndex(
							subMonitor.newChild(1));
				}
			}
		}
		
		subMonitor.done();
	}

}
