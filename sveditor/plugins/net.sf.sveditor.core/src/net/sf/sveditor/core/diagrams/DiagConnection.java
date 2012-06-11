/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.diagrams ;
	
public class DiagConnection {
	
	final String fLabel ; 
	final DiagNode fSrcNode ;
	final DiagNode fDstNode;
	final DiagConnectionType fConType;
	
	public DiagConnection(String label, DiagConnectionType conType, DiagNode srcNode , DiagNode dstNode ) {
		this.fLabel  = label ;
		this.fSrcNode  = srcNode ;
		this.fDstNode = dstNode ;
		this.fConType = conType ;
	}

	public DiagConnectionType getConType() {
		return fConType;
	}
	
	public String getLabel() {
		return fLabel ;
	}
	
	public DiagNode getSource() {
		return fSrcNode ;
	}
	public DiagNode getDestination() {
		return fDstNode;
	}

}
