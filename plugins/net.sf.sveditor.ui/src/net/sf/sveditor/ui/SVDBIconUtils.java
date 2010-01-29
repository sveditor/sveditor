package net.sf.sveditor.ui;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypedef;

import org.eclipse.swt.graphics.Image;

public class SVDBIconUtils implements ISVIcons {
	
	private static final Map<SVDBItemType, String>		fImgDescMap;
	
	static {
		fImgDescMap = new HashMap<SVDBItemType, String>();

		fImgDescMap.put(SVDBItemType.Module, MODULE_OBJ);
		fImgDescMap.put(SVDBItemType.Interface, INT_OBJ);
		fImgDescMap.put(SVDBItemType.Class, CLASS_OBJ);
		fImgDescMap.put(SVDBItemType.Macro, DEFINE_OBJ);
		fImgDescMap.put(SVDBItemType.Include, INCLUDE_OBJ);
		fImgDescMap.put(SVDBItemType.PackageDecl, PACKAGE_OBJ);
		fImgDescMap.put(SVDBItemType.Struct, STRUCT_OBJ);
		fImgDescMap.put(SVDBItemType.Covergroup, COVERGROUP_OBJ);
		fImgDescMap.put(SVDBItemType.Coverpoint, COVERPOINT_OBJ);
		fImgDescMap.put(SVDBItemType.Sequence, SEQUENCE_OBJ);
		fImgDescMap.put(SVDBItemType.Property, PROPERTY_OBJ);
		fImgDescMap.put(SVDBItemType.Constraint, CONSTRAINT_OBJ);
		fImgDescMap.put(SVDBItemType.AlwaysBlock, ALWAYS_BLOCK_OBJ);
		fImgDescMap.put(SVDBItemType.InitialBlock, INITIAL_OBJ);
		fImgDescMap.put(SVDBItemType.Assign, ASSIGN_OBJ);
	}
	
	public static Image getIcon(String key) {
		return SVUiPlugin.getImage(key);
	}
	
	public static Image getIcon(SVDBItem it) {
		if (it instanceof IFieldItemAttr) {
			int            attr = ((IFieldItemAttr)it).getAttr();
			SVDBItemType   type = ((SVDBItem)it).getType();
			
			if (type == SVDBItemType.VarDecl) {
				if (it.getParent() != null && 
						(it.getParent().getType() == SVDBItemType.Task ||
								it.getParent().getType() == SVDBItemType.Function)) {
					return SVUiPlugin.getImage(LOCAL_OBJ);
				} else {
					if ((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
						return SVUiPlugin.getImage(FIELD_PRIV_OBJ);
					} else if ((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
						return SVUiPlugin.getImage(FIELD_PROT_OBJ);
					} else {
						return SVUiPlugin.getImage(FIELD_PUB_OBJ);
					}
				}
			} else if (type == SVDBItemType.ModIfcInst) {
				return SVUiPlugin.getImage(MOD_IFC_INST_OBJ);
			} else if (type == SVDBItemType.Task || 
					type == SVDBItemType.Function) {
				if ((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
					return SVUiPlugin.getImage(TASK_PRIV_OBJ);
				} else if ((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
					return SVUiPlugin.getImage(TASK_PROT_OBJ);
				} else {
					return SVUiPlugin.getImage(TASK_PUB_OBJ);
				}
			} else if (type == SVDBItemType.TaskFuncParam) {
				return SVUiPlugin.getImage(LOCAL_OBJ);
			}
		} else if (it instanceof SVDBItem) {
			SVDBItemType type = ((SVDBItem)it).getType();
			
			if (fImgDescMap.containsKey(type)) {
				return SVUiPlugin.getImage(fImgDescMap.get(type));
			} else if (it.getType() == SVDBItemType.Typedef) {
				SVDBTypedef td = (SVDBTypedef)it;
				
				if (td.isEnumType()) {
					return SVUiPlugin.getImage(ENUM_TYPE_OBJ);
				} else {
					return SVUiPlugin.getImage(TYPEDEF_TYPE_OBJ);
				}
			}
		}
		
		return null;
	}
}
