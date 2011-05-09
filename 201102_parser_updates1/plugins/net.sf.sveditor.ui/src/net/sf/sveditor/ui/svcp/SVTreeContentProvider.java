/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.svcp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInst;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVTreeContentProvider implements ITreeContentProvider {
	
	private static final Set<SVDBItemType>		fDoNotRecurseScopes;
	
	static {
		fDoNotRecurseScopes = new HashSet<SVDBItemType>();
		fDoNotRecurseScopes.add(SVDBItemType.Function);
		fDoNotRecurseScopes.add(SVDBItemType.Task);
		fDoNotRecurseScopes.add(SVDBItemType.Coverpoint);
		fDoNotRecurseScopes.add(SVDBItemType.CoverpointCross);
	}
	
	public Object[] getChildren(Object elem) {
		if (elem instanceof ISVDBChildParent && 
				!fDoNotRecurseScopes.contains(((ISVDBChildParent)elem).getType())) {
			ISVDBChildParent cp = (ISVDBChildParent)elem;
			List<ISVDBItemBase> c = new ArrayList<ISVDBItemBase>();
			for (ISVDBChildItem it : cp.getChildren()) {
				if (it.getType() == SVDBItemType.VarDeclStmt ||
						it.getType() == SVDBItemType.ImportStmt ||
						it.getType() == SVDBItemType.ExportStmt) {
					for (ISVDBChildItem ci : ((ISVDBChildParent)it).getChildren()) {
						c.add(ci);
					}
				} else if (it.getType() == SVDBItemType.ModIfcInst) {
					for (ISVDBChildItem ci : ((SVDBModIfcInst)it).getChildren()) {
						c.add(ci);
					}
				} else {
					if (it.getType() != SVDBItemType.NullStmt) {
						c.add(it);
					}
				}
			}
			return c.toArray();
		} else {
			return new Object[0];
		}
	}
	
	public Object getParent(Object element) {
		if (element instanceof ISVDBChildItem) {
			return ((ISVDBChildItem)element).getParent();
		} else {
			return null;
		}
	}
	
	public boolean hasChildren(Object element) {
		if (element instanceof ISVDBChildParent) {
			ISVDBChildParent p = (ISVDBChildParent)element;
			if (!fDoNotRecurseScopes.contains(p.getType())) {
				return p.getChildren().iterator().hasNext();
			}
		}
		return false;
	}

	public Object[] getElements(Object element) {
		if (element instanceof ISVDBScopeItem) {
			return ((ISVDBScopeItem)element).getItems().toArray();
		} else {
			return new Object[0];
		}
	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}
}
