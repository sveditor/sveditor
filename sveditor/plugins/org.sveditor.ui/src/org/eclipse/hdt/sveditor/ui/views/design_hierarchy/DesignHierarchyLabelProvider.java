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
package org.eclipse.hdt.sveditor.ui.views.design_hierarchy;

import org.eclipse.hdt.sveditor.ui.SVDBIconUtils;
import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInst;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcInstItem;
import org.eclipse.hdt.sveditor.core.db.SVDBModuleDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBProgramDecl;
import org.eclipse.hdt.sveditor.core.design_hierarchy.DesignHierarchyNode;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class DesignHierarchyLabelProvider extends LabelProvider {

	@Override
	public Image getImage(Object element) {
		if (element instanceof DesignHierarchyNode) {
			DesignHierarchyNode dn = (DesignHierarchyNode)element;
			Object target = dn.getTarget();
			
			if (target instanceof SVDBModIfcInstItem) {
				return SVUiPlugin.getImage(SVDBIconUtils.MOD_IFC_INST_OBJ);
			} else if (target instanceof SVDBModuleDecl) {
				return SVUiPlugin.getImage(SVDBIconUtils.MODULE_OBJ);
			} else if (target instanceof SVDBProgramDecl) {
				return SVUiPlugin.getImage(SVDBIconUtils.PROGRAM_OBJ);
			}
		} else if (element instanceof IProject) {
			return SVUiPlugin.getImage("/icons/obj16/prj_obj.gif");
		}
		// TODO Auto-generated method stub
		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof DesignHierarchyNode) {
			DesignHierarchyNode dn = (DesignHierarchyNode)element;
			Object target = dn.getTarget();
			
			if (target instanceof SVDBModIfcInstItem) {
				SVDBModIfcInstItem inst_item = (SVDBModIfcInstItem)target;
				String inst_name = inst_item.getName();
				String type_name = ((SVDBModIfcInst)inst_item.getParent()).getTypeName();
				
				return inst_name + " : " + type_name;
			} else if (target instanceof SVDBModIfcDecl) {
				return ((SVDBModIfcDecl)target).getName();
			}
		} else if (element instanceof IProject) {
			return ((IProject)element).getName();
		}
		return super.getText(element);
	}
	
	public String getName(Object element) {
		if (element instanceof DesignHierarchyNode) {
			DesignHierarchyNode dn = (DesignHierarchyNode)element;
			Object target = dn.getTarget();
			
			if (target instanceof SVDBModIfcInstItem) {
				SVDBModIfcInstItem inst_item = (SVDBModIfcInstItem)target;
				return inst_item.getName();
			} else if (target instanceof SVDBModIfcDecl) {
				return ((SVDBModIfcDecl)target).getName();
			}
		} else if (element instanceof IProject) {
			return ((IProject)element).getName();
		}		
		
		return "";
	}
	
}
