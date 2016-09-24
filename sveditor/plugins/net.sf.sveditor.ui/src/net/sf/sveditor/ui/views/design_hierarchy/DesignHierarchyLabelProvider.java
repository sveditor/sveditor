package net.sf.sveditor.ui.views.design_hierarchy;

import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.SVDBProgramDecl;
import net.sf.sveditor.core.design_hierarchy.DesignHierarchyNode;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
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
