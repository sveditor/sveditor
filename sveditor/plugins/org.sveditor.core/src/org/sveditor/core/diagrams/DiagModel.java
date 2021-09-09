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

package org.sveditor.core.diagrams;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;


public class DiagModel {
	
	private List<DiagConnection> connections ;
	private List<DiagNode> nodes ;
	
	private HashMap<String,DiagNode> fClassNodeMap ;
	
	public DiagNode getVisitedClass(String className) {
		if(fClassNodeMap.containsKey(className)) {
			return fClassNodeMap.get(className) ;
		} else {
			return null ;
		}
	}
	
	public void addNode(DiagNode node) {
		fClassNodeMap.put(node.getName(), node) ;
		nodes.add(node) ;
	}
	
	public void addConnection(DiagConnection con) {
		connections.add(con) ;
	}
	
	public DiagModel() {
		
		nodes = new ArrayList<DiagNode>() ;
		connections = new ArrayList<DiagConnection>() ;
		fClassNodeMap = new HashMap<String, DiagNode>() ;
		
	}

	public List<DiagNode> getNodes() {
		return nodes;
	}	

}
