/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial contributor 
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram;

import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.diagrams.DiagConnection;
import net.sf.sveditor.core.diagrams.DiagNode;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.zest.core.viewers.EntityConnectionData;
import org.eclipse.zest.core.viewers.IConnectionStyleProvider;
import org.eclipse.zest.core.viewers.IFigureProvider;
import org.eclipse.zest.core.widgets.ZestStyles;

public class DiagLabelProvider extends AbstractDiagLabelProvider implements IFigureProvider, IConnectionStyleProvider {
	
	@Override
	public String getText(Object element) {
		if (element instanceof DiagNode) {
			DiagNode myNode = (DiagNode) element;
			return myNode.getName();
		}
		if (element instanceof DiagConnection) {
			DiagConnection myConnection = (DiagConnection) element;
			return myConnection.getLabel();
		}
		if (element instanceof EntityConnectionData) {
			// TODO: optionally return member name for composition relationships
			return "";
		}
		throw new RuntimeException("Unexpected type: " + element.getClass().toString());
	}
	
	@Override
	public Image getImage(Object element) {
		if (element instanceof DiagNode) {
			DiagNode myNode = (DiagNode) element;
			// TODO: Check also for interfaces
			if(myNode.getSVDBItem().getType() == SVDBItemType.ClassDecl) {
				return SVDBIconUtils.getIcon(myNode.getSVDBItem()) ;
			}
		}
		return null ;
	}

	@Override
	public IFigure getFigure(Object element) {
		if (element instanceof DiagNode) {
			DiagNode myNode = (DiagNode) element;
			if(myNode.getSVDBItem().getType() == SVDBItemType.ClassDecl) {
				return createClassFigure(myNode) ;
			}
		}
		return null ;
	}
	
	public IFigure createClassFigure(DiagNode node) {
		
		if(node.getSVDBItem().getType() != SVDBItemType.ClassDecl) {
			return null ;
		}
		
		SVDBClassDecl classDecl = (SVDBClassDecl)node.getSVDBItem() ;
		
		Label classLabel1 = new Label(classDecl.getName(), SVDBIconUtils.getIcon(classDecl)) ;
//		classLabel1.setFont(classFont);
		
		UMLClassFigure classFigure = new UMLClassFigure(classLabel1);
		
		if(getIncludePrivateClassFields()) {
			for(SVDBVarDeclItem declItem: node.getMemberDecls()) {
				String typeName = "unknown" ;
				if(declItem.getParent() != null) {
					typeName = declItem.getParent().getTypeName();
				}
			  classFigure.getAttributesCompartment().add(new Label(typeName + ": " + declItem.getName(), SVDBIconUtils.getIcon(declItem))) ;
			}
		}
		
		if(getIncludePrivateTasksFunctions()) {
			for(SVDBFunction funcItem: node.getFuncDecls()) {
			  classFigure.getMethodsCompartment().add(new Label(funcItem.getName(), SVDBIconUtils.getIcon(funcItem))) ;
			}
		}
		
		classFigure.setSize(-1,-1) ;
		
		return classFigure ;
	}

	@Override
	public int getConnectionStyle(Object rel) {
		int res = 0 ;
		if(rel instanceof EntityConnectionData) {
			EntityConnectionData ecd = (EntityConnectionData)rel ;
			if(ecd.source instanceof DiagNode && ecd.dest instanceof DiagNode) {
				DiagNode srcNode = (DiagNode)ecd.source ;
				DiagNode dstNode = (DiagNode)ecd.dest ;
				if(srcNode.getSuperClasses().contains(dstNode)) {
					res |= ZestStyles.CONNECTIONS_SOLID ;
				} else {
					res |= ZestStyles.CONNECTIONS_DASH ;
				}
			}
		}
		res |= ZestStyles.CONNECTIONS_DIRECTED ;
		return res ;
	}

	@Override
	public Color getColor(Object rel) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Color getHighlightColor(Object rel) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getLineWidth(Object rel) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public IFigure getTooltip(Object entity) {
		// TODO Auto-generated method stub
		return null;
	}
	
}
