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

import net.sf.sveditor.core.diagrams.DiagNode;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.zest.core.viewers.IGraphEntityContentProvider;

public class NodeContentProvider extends ArrayContentProvider implements IGraphEntityContentProvider {
	
	@Override
	public Object[] getConnectedTo(Object entity) {
		if (entity instanceof DiagNode) {
			DiagNode node = (DiagNode) entity;
			return node.getConnectedTo().toArray();
		}
		throw new RuntimeException("Type not supported");
	}

//	@Override
//	public boolean hasChildren(Object element) {
//	   if(element instanceof DiagNode)	{
//		 return ((DiagNode)element).getChildren().size() != 0 ;
//	   } else {
//		return false;
//	   }
//	}
//
//	@Override
//	public Object[] getChildren(Object element) {
//	   if(element instanceof DiagNode)	{
//		 return ((DiagNode)element).getChildren().toArray() ;
//	   } else {
//		return null;
//	   }
//	}
	
}
