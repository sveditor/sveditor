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

import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.search.SVDBFindClassDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.diagrams.DiagConnection;
import net.sf.sveditor.core.diagrams.DiagConnectionType;
import net.sf.sveditor.core.diagrams.DiagNode;

public abstract class AbstractDiagModelFactory implements IDiagModelFactory {
	
	protected List<ISVDBIndex> fProjectIndexList ;
	
	
	public AbstractDiagModelFactory(List<ISVDBIndex> projectIndexList) {
		fProjectIndexList = projectIndexList ;
	}

	public DiagNode createNodeForClass(DiagModel model, SVDBClassDecl classDecl) {
		DiagNode node = model.getVisitedClass(classDecl.getName()) ;
		if(node != null) {
			return node ;
		}
		node = new DiagNode(classDecl.getName(), classDecl) ;
		model.addNode(node) ;
		for(ISVDBChildItem child: classDecl.getChildren()) {
			if(child.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt childVarDecl = (SVDBVarDeclStmt)child ;
				for(ISVDBChildItem var: childVarDecl.getChildren()) {
					if(var instanceof SVDBVarDeclItem) {
						SVDBVarDeclItem declItem = (SVDBVarDeclItem)var ;
						node.addMember(declItem) ;
					}
				}
			} else if(child.getType() == SVDBItemType.Function) {
				SVDBFunction funcItem = (SVDBFunction)child ;
				node.addFunction(funcItem) ;
			}
			
		}		
		return node ;
	}
	
	public void createNodesAndConnectionsForContainedClasses(DiagModel model, DiagNode node) {
		if(node.getSVDBItem() == null || node.getSVDBItem().getType() != SVDBItemType.ClassDecl) {
			return ;
		}
		SVDBClassDecl classDecl = (SVDBClassDecl)node.getSVDBItem() ;
		for(ISVDBChildItem child: classDecl.getChildren()) {
			if(child.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt childVarDecl = (SVDBVarDeclStmt)child ;
				// Check for members of user defined type (class?) as
				// connected to
				if(childVarDecl.getTypeInfo().getType() == SVDBItemType.TypeInfoUserDef) {
					for(ISVDBIndex svdbIndex: fProjectIndexList) {
						SVDBFindNamedClass finder = new SVDBFindNamedClass(svdbIndex, SVDBFindClassDefaultNameMatcher.getDefault()) ;
						List<SVDBClassDecl> classDecls = finder.find(childVarDecl.getTypeName()) ;
						if(classDecls.size() != 0) {
							DiagNode kidNode = createNodeForClass(model, (SVDBClassDecl)classDecls.toArray()[0]) ;
							DiagConnection con = new DiagConnection("bla", DiagConnectionType.Contains, node, kidNode) ;
							model.addConnection(con) ;
							node.addContainedClass(kidNode) ;
						}
					}
				}
			} else if(child.getType() == SVDBItemType.Function) {
				SVDBFunction funcItem = (SVDBFunction)child ;
				node.addFunction(funcItem) ;
			}
			
		}		
		
	}

	
}