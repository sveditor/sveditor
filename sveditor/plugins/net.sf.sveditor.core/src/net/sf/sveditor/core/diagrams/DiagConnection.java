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
