/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Armond Paiva - initial contributor 
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram;

import org.eclipse.hdt.sveditor.core.diagrams.DiagNode;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.zest.core.viewers.IGraphEntityContentProvider;

public class DiagContentProvider extends ArrayContentProvider implements IGraphEntityContentProvider {
	
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
