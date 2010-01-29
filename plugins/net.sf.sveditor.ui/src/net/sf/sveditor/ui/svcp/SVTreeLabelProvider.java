package net.sf.sveditor.ui.svcp;

import net.sf.sveditor.core.db.SVDBAlwaysBlock;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

public class SVTreeLabelProvider extends LabelProvider {
	
	public SVTreeLabelProvider() {
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof SVDBItem) {
			return SVDBIconUtils.getIcon((SVDBItem)element);
		} else {
			return super.getImage(element);
		}
	}
	
	@Override
	public String getText(Object element) {
		if (element instanceof SVDBItem) {
			String ret = ((SVDBItem)element).getName();
			
			if (element instanceof SVDBVarDeclItem) {
				SVDBVarDeclItem var = (SVDBVarDeclItem)element;
				
				ret = ret + " : " + ((SVDBVarDeclItem)element).getTypeName();
				SVDBTypeInfo type = var.getTypeInfo();
				
				if (type.getParameters() != null && type.getParameters().size() > 0) {
					ret += "<";
					
					for (int i=0; i<type.getParameters().size(); i++) {
						SVDBModIfcClassParam p = type.getParameters().get(i);
						ret += p.getName();
						if (i+1 < type.getParameters().size()) {
							ret += ", ";
						}
					}
					
					ret += ">";
				}
			} else if (element instanceof SVDBTaskFuncScope) {
				SVDBTaskFuncScope tf = (SVDBTaskFuncScope)element;
				
				ret = ret + "(";
				for (SVDBTaskFuncParam p : tf.getParams()) {
					ret = ret + p.getTypeName() + ", ";
				}
				
				if (ret.endsWith(", ")) {
					ret = ret.substring(0, ret.length()-2);
				}
				ret += ")";
				
				if (tf.getType() == SVDBItemType.Function && 
						tf.getReturnType() != null && 
						!tf.getReturnType().equals("void")) {
					ret += ": " + tf.getReturnType();
				}
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
			} if (element instanceof SVDBAlwaysBlock) {
				if (ret.equals("")) {
					ret = ((SVDBAlwaysBlock)element).getExpr().trim();
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
