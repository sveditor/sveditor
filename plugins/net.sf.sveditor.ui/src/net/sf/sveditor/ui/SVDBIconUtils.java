package net.sf.sveditor.ui;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.graphics.Image;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

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
	}
	
	public static Image getIcon(SVDBItem it) {
		if (it instanceof IFieldItemAttr) {
			int            attr = ((IFieldItemAttr)it).getAttr();
			SVDBItemType   type = ((SVDBItem)it).getType();
			
			if (type == SVDBItemType.VarDecl) {
				if ((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
					System.out.println("field \"" + it.getName() + "\" is private");
					return Activator.getImage(FIELD_PRIV_OBJ);
				} else if ((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
					return Activator.getImage(FIELD_PROT_OBJ);
				} else {
					return Activator.getImage(FIELD_PUB_OBJ);
				}
			} else if (type == SVDBItemType.ModIfcInst) {
				return Activator.getImage(MOD_IFC_INST_OBJ);
			} else if (type == SVDBItemType.Task) {
				if ((attr & IFieldItemAttr.FieldAttr_Local) != 0) {
					return Activator.getImage(TASK_PRIV_OBJ);
				} else if ((attr & IFieldItemAttr.FieldAttr_Protected) != 0) {
					return Activator.getImage(TASK_PROT_OBJ);
				} else {
					return Activator.getImage(TASK_PUB_OBJ);
				}
			}
		} else if (it instanceof SVDBItem) {
			SVDBItemType type = ((SVDBItem)it).getType();
			
			if (fImgDescMap.containsKey(type)) {
				return Activator.getImage(fImgDescMap.get(type));
			}
		}
		
		return null;
	}
}
