package net.sf.sveditor.ui.svcp;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.ui.Activator;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class SVTreeLabelProvider extends LabelProvider {
	private Map<SVDBItemType, String>			fImgDescMap;
	private Map<String, Image>			fImgMap;
	
	public SVTreeLabelProvider() {
		String obj_icons = "icons/edecl16/";
		fImgDescMap = new HashMap<SVDBItemType, String>();
		fImgMap = new HashMap<String, Image>();
		
		fImgDescMap.put(SVDBItemType.Module, obj_icons + "module_obj.gif");
		fImgDescMap.put(SVDBItemType.Interface, obj_icons + "int_obj.gif");
		fImgDescMap.put(SVDBItemType.Class, obj_icons + "class_obj.gif");
		fImgDescMap.put(SVDBItemType.Macro, obj_icons + "define_obj.gif");
		fImgDescMap.put(SVDBItemType.Include, obj_icons + "include_obj.gif");
		fImgDescMap.put(SVDBItemType.PackageDecl, obj_icons + "package.gif");
		fImgDescMap.put(SVDBItemType.Struct, obj_icons + "struct_obj.gif");
	}

	@Override
	public Image getImage(Object element) {

		if (element instanceof SVDBFieldItem) {
			SVDBFieldItem field_item = (SVDBFieldItem)element;
			SVDBItemType type = field_item.getType();
			
			if (type == SVDBItemType.VarDecl) {
				if ((field_item.getAttr() & SVDBFieldItem.FieldAttr_Local) != 0) {
					return getImage("icons/edecl16/field_private_obj.gif");
				} else if ((field_item.getAttr() & SVDBFieldItem.FieldAttr_Protected) != 0) {
					return getImage("icons/edecl16/field_protected_obj.gif");
				} else {
					return getImage("icons/edecl16/field_public_obj.gif");
				}
			} else if (type == SVDBItemType.Task) {
				if ((field_item.getAttr() & SVDBFieldItem.FieldAttr_Local) != 0) {
					return getImage("icons/edecl16/private_co.gif");
				} else if ((field_item.getAttr() & SVDBFieldItem.FieldAttr_Protected) != 0) {
					return getImage("icons/edecl16/protected_co.gif");
				} else {
					return getImage("icons/edecl16/public_co.gif");
				}
			}
		} else if (element instanceof SVDBItem) {
			SVDBItemType type = ((SVDBItem)element).getType();
			
			if (fImgDescMap.containsKey(type)) {
				return getImage(fImgDescMap.get(type));
			}
		}
		
		return super.getImage(element);
	}
	
	private Image getImage(String key) {
		if (!fImgMap.containsKey(key)) {
			Image img;
			img = Activator.imageDescriptorFromPlugin(
					Activator.PLUGIN_ID, key).createImage();
			fImgMap.put(key, img);
		}
		return fImgMap.get(key);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof SVDBItem) {
			String ret = ((SVDBItem)element).getName();
			
			if (element instanceof SVDBVarDeclItem) {
				ret = ret + " : " + ((SVDBVarDeclItem)element).getTypeName();
			} else if (element instanceof SVDBTaskFuncScope) {
				SVDBTaskFuncScope tf = (SVDBTaskFuncScope)element;
				
				ret = ret + " : (";
				for (SVDBTaskFuncParam p : tf.getParams()) {
					ret = ret + p.getTypeName() + ", ";
				}
				
				if (ret.endsWith(", ")) {
					ret = ret.substring(0, ret.length()-2);
				}
				ret += ")";
			} else if (element instanceof SVDBModIfcClassDecl) {
				SVDBModIfcClassDecl decl = (SVDBModIfcClassDecl)element;

				if (decl.getParameters().size() > 0) {
					ret += "<";
					
					for (SVDBModIfcClassParam p : decl.getParameters()) {
						ret = ret + p.getName() + ", ";
					}
					
					if (ret.endsWith(", ")) {
						ret = ret.substring(0, ret.length()-2);
					}
					
					ret += ">";
				}
			}
			
			return ret; 
		} else {
			return element.toString();
		}
	}

	@Override
	public void dispose() {
		super.dispose();
		
	}
	
}
