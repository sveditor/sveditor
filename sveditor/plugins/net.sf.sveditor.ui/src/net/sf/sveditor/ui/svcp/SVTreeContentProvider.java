/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.ui.argfile.editor.outline.SVArgFileOutlineContent;
import net.sf.sveditor.ui.editor.outline.SVOutlineContent;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class SVTreeContentProvider implements ITreeContentProvider {
	
	private static final Set<SVDBItemType>		fDoNotRecurseScopes;
	private static final Set<SVDBItemType>		fExpandInLineItems;
	private static final Set<SVDBItemType>		fIgnoreItems;
	private ISVDBChildParent					fRoot;
	
	static {
		fDoNotRecurseScopes = new HashSet<SVDBItemType>();
		fDoNotRecurseScopes.add(SVDBItemType.Function);
		fDoNotRecurseScopes.add(SVDBItemType.Task);
		fDoNotRecurseScopes.add(SVDBItemType.Coverpoint);
		fDoNotRecurseScopes.add(SVDBItemType.CoverpointCross);
		fDoNotRecurseScopes.add(SVDBItemType.Constraint);
		fDoNotRecurseScopes.add(SVDBItemType.ConfigDecl);
		
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
	
	public Object[] getChildren(Object elem) {
		int file_id = -1;
		
		if (fRoot != null && fRoot.getLocation() != null) {
			file_id = fRoot.getLocation().getFileId();
		}
		
		if (elem instanceof ISVDBItemBase) {
			List<ISVDBItemBase> c = new ArrayList<ISVDBItemBase>();
			ISVDBItemBase it = (ISVDBItemBase)elem;
			
			if (it instanceof ISVDBChildParent && 
					!fDoNotRecurseScopes.contains(it.getType())) {
				for (ISVDBChildItem ci : ((ISVDBChildParent)it).getChildren()) {
					if (file_id != -1 && ci.getLocation() != null) {
						if (file_id != ci.getLocation().getFileId()) {
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
