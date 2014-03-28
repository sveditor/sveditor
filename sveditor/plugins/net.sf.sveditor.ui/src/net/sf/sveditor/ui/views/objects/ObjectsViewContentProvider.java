/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 *     Armond Paiva - repurposed from hierarchy to objects view
 ****************************************************************************/


package net.sf.sveditor.ui.views.objects;

import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.objects.ObjectsTreeFactory;
import net.sf.sveditor.core.objects.ObjectsTreeNode;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

public class ObjectsViewContentProvider implements ITreeContentProvider {
	private static final Object 		fEmptyArray[] = new Object[0];
	private SVDBIndexRegistry fIndexRegistry ;
	
	private ObjectsTreeNode         fNodeModules;
	private ObjectsTreeNode         fNodeInterface;
	private ObjectsTreeNode         fNodePackages;
	
	public ObjectsTreeNode getModulesNode() {
		return fNodeModules ;
	}
	public ObjectsTreeNode getInterfacesNode() {
		return fNodeInterface ;
	}
	public ObjectsTreeNode getPackagesNode() {
		return fNodePackages ;
	}
	
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof ObjectsTreeNode) {
			return ((ObjectsTreeNode)parentElement).getChildren().toArray();
		} else {
			return fEmptyArray;
		}
	}

	public Object getParent(Object element) {
		if (element instanceof ObjectsTreeNode) {
			return ((ObjectsTreeNode)element).getParent();
		} else {
			return null;
		}
	}

	public boolean hasChildren(Object element) {
		if (element instanceof ObjectsTreeNode) {
			return (((ObjectsTreeNode)element).getChildren().size() > 0);
		} else {
			return false;
		}
	}

	public Object[] getElements(Object inputElement) {
		List<ISVDBIndex> projectIndexList = fIndexRegistry.getAllProjectLists() ; 
		ObjectsTreeFactory factory = new ObjectsTreeFactory(projectIndexList) ;
		ObjectsTreeNode topNode = factory.build();
		if(topNode == null)  {
			return fEmptyArray ;
		} else {
			fNodeInterface = topNode.getChildByName(ObjectsTreeNode.INTERFACES_NODE) ;
			fNodeModules = topNode.getChildByName(ObjectsTreeNode.MODULES_NODE) ;
			fNodePackages = topNode.getChildByName(ObjectsTreeNode.PACKAGES_NODE) ;			
			return topNode.getChildren().toArray() ;
		}
		
	}

	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		fIndexRegistry = (SVDBIndexRegistry)newInput ; 
	}

}
