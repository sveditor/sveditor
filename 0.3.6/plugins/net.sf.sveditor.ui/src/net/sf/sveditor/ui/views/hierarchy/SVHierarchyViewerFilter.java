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


package net.sf.sveditor.ui.views.hierarchy;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

public class SVHierarchyViewerFilter extends ViewerFilter {
	private HierarchyTreeNode		fTarget;
	private boolean					fShowInheritedMembers;
	private boolean					fHideFields;
	private boolean					fHideStatic;
	private boolean					fHideNonPublic;
	
	public void setTarget(HierarchyTreeNode target) {
		fTarget = target;
	}
	
	public void setShowInheritedMembers(boolean show) {
		fShowInheritedMembers = show;
	}
	
	public void setHideFields(boolean hide) {
		fHideFields = hide;
	}
	
	public void setHideStatic(boolean hide) {
		fHideStatic = hide;
	}
	
	public void setHideNonPublic(boolean hide) {
		fHideNonPublic = hide;
	}

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		if (fTarget == null) {
			return true;
		}
		
		if (element instanceof SVDBItem) {
			SVDBItem it = (SVDBItem)element;
			
			if (!fShowInheritedMembers) {
				if (fTarget.getItemDecl().getType() == SVDBItemType.Class) {
					if (!isInScope((SVDBModIfcClassDecl)fTarget.getItemDecl(), it)) {
						return false;
					}
				}
			}
			
			if (fHideFields && it.getType() == SVDBItemType.VarDecl) {
				return false;
			}

			if (fHideStatic) {
				if (it instanceof SVDBFieldItem &&
						(((SVDBFieldItem)it).getAttr() & IFieldItemAttr.FieldAttr_Static) != 0) {
					return false;
				} else if (it instanceof SVDBTaskFuncScope &&
						(((SVDBTaskFuncScope)it).getAttr() & IFieldItemAttr.FieldAttr_Static) != 0) {
					return false;
				}
			}
			
			if (fHideNonPublic) {
				if (it instanceof SVDBFieldItem &&
						((((SVDBFieldItem)it).getAttr() & IFieldItemAttr.FieldAttr_Local) != 0 || 
						 (((SVDBFieldItem)it).getAttr() & IFieldItemAttr.FieldAttr_Protected) != 0)) {
					return false;
				} else if (it instanceof SVDBTaskFuncScope &&
						((((SVDBTaskFuncScope)it).getAttr() & IFieldItemAttr.FieldAttr_Local) != 0 ||
						 (((SVDBTaskFuncScope)it).getAttr() & IFieldItemAttr.FieldAttr_Protected) != 0)) {
					return false;
				}
			}
		}
		
		return true;
	}
	
	private boolean isInScope(ISVDBScopeItem scope, SVDBItem it) {
		
		for (SVDBItem it_t : scope.getItems()) {
			if (it_t == it) {
				return true;
			} else if (it_t instanceof ISVDBScopeItem) {
				if (isInScope((ISVDBScopeItem)it_t, it)) {
					return true;
				}
			}
		}
		
		return false;
	}

}
