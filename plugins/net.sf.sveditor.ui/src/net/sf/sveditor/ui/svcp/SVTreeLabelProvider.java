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

import net.sf.sveditor.core.db.SVDBAlwaysBlock;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class SVTreeLabelProvider extends LabelProvider {
	private WorkbenchLabelProvider				fLabelProvider;
	
	
	public SVTreeLabelProvider() {
		fLabelProvider = new WorkbenchLabelProvider();
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
				
				if (var.getTypeInfo() != null) {
					ret = ret + " : " + var.getTypeName();
					
					SVDBTypeInfo type = var.getTypeInfo();
					
					if (type.getDataType() == SVDBDataType.UserDefined) {
						SVDBTypeInfoUserDef cls = (SVDBTypeInfoUserDef)type;
						if (cls.getParameters() != null && 
								cls.getParameters().getParameters().size() > 0) {
							ret += "<";
							
							for (int i=0; i<cls.getParameters().getParameters().size(); i++) {
								SVDBParamValueAssign p = 
									cls.getParameters().getParameters().get(i);
								ret += p.getName();
								if (i+1 < cls.getParameters().getParameters().size()) {
									ret += ", ";
								}
							}
							
							ret += ">";
						}
					}
				}
			} else if (element instanceof SVDBTaskFuncScope) {
				SVDBTaskFuncScope tf = (SVDBTaskFuncScope)element;
				
				ret = ret + "(";
				for (SVDBParamPort p : tf.getParams()) {
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
	public void addListener(ILabelProviderListener listener) {
		fLabelProvider.addListener(listener);
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
		fLabelProvider.removeListener(listener);
	}
	
	@Override
	public boolean isLabelProperty(Object element, String property) {
		return fLabelProvider.isLabelProperty(element, property);
	}

	@Override
	public void dispose() {
		super.dispose();
		fLabelProvider.dispose();
	}

}
