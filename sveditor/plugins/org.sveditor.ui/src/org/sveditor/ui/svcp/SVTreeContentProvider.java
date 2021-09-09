/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.ui.svcp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.sveditor.ui.argfile.editor.outline.SVArgFileOutlineContent;
import org.sveditor.ui.editor.outline.SVOutlineContent;

import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.ISVDBChildParent;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVTreeContentProvider implements ITreeContentProvider {
	
	public static final Set<SVDBItemType>		fDoNotRecurseScopes;
	public static final Set<SVDBItemType>		fExpandInLineItems;
	public static final Set<SVDBItemType>		fIgnoreItems;
	private ISVDBChildParent					fRoot;
	
	static {
		fDoNotRecurseScopes = new HashSet<SVDBItemType>();
		fDoNotRecurseScopes.add(SVDBItemType.Function);
		fDoNotRecurseScopes.add(SVDBItemType.Task);
		fDoNotRecurseScopes.add(SVDBItemType.Coverpoint);
		fDoNotRecurseScopes.add(SVDBItemType.CoverpointCross);
		fDoNotRecurseScopes.add(SVDBItemType.Constraint);
		fDoNotRecurseScopes.add(SVDBItemType.ConfigDecl);
		fDoNotRecurseScopes.add(SVDBItemType.AlwaysStmt);
		
		fExpandInLineItems = new HashSet<SVDBItemType>();
		fExpandInLineItems.add(SVDBItemType.VarDeclStmt);
		fExpandInLineItems.add(SVDBItemType.ParamPortDecl);
		fExpandInLineItems.add(SVDBItemType.ModIfcInst);
		fExpandInLineItems.add(SVDBItemType.ImportStmt);
		fExpandInLineItems.add(SVDBItemType.ExportStmt);
		fExpandInLineItems.add(SVDBItemType.DefParamStmt);
		
		fIgnoreItems = new HashSet<SVDBItemType>();
		fIgnoreItems.add(SVDBItemType.NullStmt);
	}

	@SuppressWarnings("rawtypes")
	public Object[] getChildren(Object elem) {
		int file_id = -1;
		
		if (fRoot != null && fRoot.getLocation() != -1) {
			file_id = SVDBLocation.unpackFileId(fRoot.getLocation());
		}
		
		if (elem instanceof SVDBDeclCacheItem) {
			elem = ((SVDBDeclCacheItem)elem).getSVDBItem();
		}
		
		if (elem instanceof ISVDBItemBase) {
			List<ISVDBItemBase> c = new ArrayList<ISVDBItemBase>();
			ISVDBItemBase it = (ISVDBItemBase)elem;
			
			if (it instanceof ISVDBChildParent && 
					!fDoNotRecurseScopes.contains(it.getType())) {
				for (ISVDBChildItem ci : ((ISVDBChildParent)it).getChildren()) {
					if (file_id != -1 && ci.getLocation() != -1) {
						if (file_id != SVDBLocation.unpackFileId(ci.getLocation())) {
							continue;
						}
					}
					if (fExpandInLineItems.contains(ci.getType())) {
						for (ISVDBChildItem ci_p : ((ISVDBChildParent)ci).getChildren()) {
							c.add(ci_p);
						}
					} else if (!fIgnoreItems.contains(ci.getType())) {
						c.add(ci);
					}
				}
			} else {
//				System.out.println("elem instanceof " + (elem instanceof ISVDBChildParent));
			}
		
			return c.toArray();
		} else if (elem instanceof List) {
			return ((List)elem).toArray();
		} else {
			
		}
		
		return new Object[0];
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
		return getChildren(element);
	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput instanceof SVOutlineContent) {
			fRoot = ((SVOutlineContent)newInput).getFile();
		} else if (newInput instanceof SVArgFileOutlineContent) {
			fRoot = ((SVArgFileOutlineContent)newInput).getFile();
		} else if (newInput instanceof ISVDBChildParent) {
			fRoot = (ISVDBChildParent)newInput;
		}
	}
}
