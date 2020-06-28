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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

public class DiagNode {
	
	private final String fName ;
	
	private HashSet<DiagNode> fSuperClasses ;
	private HashSet<DiagNode> fContainedClasses ;
	
	private ISVDBItemBase fISVDBItem ;

	private List<SVDBVarDeclItem> fMemberDecls ;
	private List<SVDBFunction> fFuncDecls ;
	private List<SVDBTask> fTaskDecls ;
	
	private boolean fSelected ;

	public DiagNode(String name, ISVDBItemBase item) {

		this.fName = name;
		this.fSelected = false;
		this.fMemberDecls = new ArrayList<SVDBVarDeclItem>();
		this.fFuncDecls = new ArrayList<SVDBFunction>();
		this.fTaskDecls = new ArrayList<SVDBTask>();
		this.fISVDBItem = item ;
		this.fSuperClasses = new HashSet<DiagNode>() ;
		this.fContainedClasses = new HashSet<DiagNode>() ;
	}

	public String getName() {
		return fName ;
	}
	
	public void addMember(SVDBVarDeclItem declItem) {
		fMemberDecls.add(declItem) ;
	}
	
	public void addSuperClass(DiagNode node) {
		fSuperClasses.add(node) ;
	}
	
	public void addContainedClass(DiagNode node) {
		fContainedClasses.add(node) ;
	}
	
	public Collection<DiagNode> getSuperClasses() {
		return fSuperClasses ;
	}
	
	public Collection<DiagNode> getContainedClasses() {
		return fContainedClasses ;
	}
	
	public List<SVDBVarDeclItem> getMemberDecls() {
		return fMemberDecls ;
	}
	
	public ISVDBItemBase getSVDBItem() {
		return fISVDBItem ; 
	}

	public List<DiagNode> getConnectedTo() {
		List<DiagNode> connections = new ArrayList<DiagNode>(fSuperClasses) ;
		connections.addAll(new ArrayList<DiagNode>(fContainedClasses)) ;
		return connections ;
	}	

	public void addFunction(SVDBFunction funcItem) {
		this.fFuncDecls.add(funcItem) ;
	}
	
	public List<SVDBFunction> getFuncDecls() {
		return fFuncDecls ;
	}

	public void addTask(SVDBTask taskItem) {
		this.fTaskDecls.add(taskItem) ;
	}
	
	public List<SVDBTask> getTaskDecls() {
		return fTaskDecls ;
	}

	public void setSelected(boolean selected) {
		fSelected = selected ;
	}

	public boolean getSelected() {
		return fSelected ;
	}

}
