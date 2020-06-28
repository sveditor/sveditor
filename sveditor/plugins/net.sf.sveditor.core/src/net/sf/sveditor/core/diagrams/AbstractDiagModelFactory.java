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

package net.sf.sveditor.core.diagrams;

import java.util.HashMap;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindClassDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;

public abstract class AbstractDiagModelFactory implements IDiagModelFactory {
	
	protected ISVDBIndex fIndex ;
	
	
	public AbstractDiagModelFactory(ISVDBIndex index) {
		fIndex = index ;
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
			} else if(child.getType() == SVDBItemType.Task) {
				SVDBTask taskItem = (SVDBTask)child ;
				node.addTask(taskItem) ;
			}
			
		}		
		return node ;
	}

	public DiagNode createNodeForModule(DiagModel model, SVDBModIfcDecl moduleDecl) {
		DiagNode node = model.getVisitedClass(moduleDecl.getName()) ;
		if(node != null) {
			return node ;
		}
		node = new DiagNode(moduleDecl.getName(), moduleDecl) ;
		model.addNode(node) ;
		// TODO: show ports?
		if (moduleDecl.getPorts() != null) {
			
		}
		for(ISVDBChildItem child: moduleDecl.getChildren()) {
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
			} else if(child.getType() == SVDBItemType.Task) {
				SVDBTask taskItem = (SVDBTask)child ;
				node.addTask(taskItem) ;
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
					SVDBFindNamedClass finder = new SVDBFindNamedClass(fIndex, SVDBFindClassDefaultNameMatcher.getDefault()) ;
					List<SVDBClassDecl> classDecls = finder.findItem(childVarDecl.getTypeName()) ;
					if(classDecls.size() != 0) {
						DiagNode kidNode = createNodeForClass(model, (SVDBClassDecl)classDecls.toArray()[0]) ;
						DiagConnection con = new DiagConnection("bla", DiagConnectionType.Contains, node, kidNode) ;
						model.addConnection(con) ;
						node.addContainedClass(kidNode) ;
					}
				}
			}
			
		}		
	}

	public void createNodesAndConnectionsForContainedModules(DiagModel model, DiagNode node) {
		if(node.getSVDBItem() == null || node.getSVDBItem().getType() != SVDBItemType.ModuleDecl) {
			return ;
		}
		SVDBModuleDecl moduleDecl = (SVDBModuleDecl)node.getSVDBItem();
		for(ISVDBChildItem child: moduleDecl.getChildren()) {
			if(child.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInst modInst = (SVDBModIfcInst)child;
				
				// Check for members of user defined type (class?) as
				// connected to
				SVDBFindNamedModIfcClassIfc finder = new SVDBFindNamedModIfcClassIfc(fIndex);
				List<SVDBDeclCacheItem> result = finder.findItems(modInst.getTypeName());
			
				if (result.size() > 0 && result.get(0).getType() == SVDBItemType.ModuleDecl) {
					DiagNode kidNode = createNodeForModule(model, 
							(SVDBModuleDecl)result.get(0).getSVDBItem());
					DiagConnection con = new DiagConnection("bla", DiagConnectionType.Contains, node, kidNode) ;
					model.addConnection(con) ;
					node.addContainedClass(kidNode) ;
				}
			}
		}		
	}
	
	public void createConnectionsForNodes(DiagModel model, List<DiagNode> nodes) {
		HashMap<String,DiagNode> nodeHash = new HashMap<String,DiagNode>() ;
		for(DiagNode node: nodes) {
			nodeHash.put(node.getName(), node) ;
		}
		
		for(DiagNode node: nodes) {
			SVDBClassDecl classDecl = (SVDBClassDecl)node.getSVDBItem() ;
			for(ISVDBChildItem child: classDecl.getChildren()) {
				if(child.getType() == SVDBItemType.VarDeclStmt) {
					SVDBVarDeclStmt childVarDecl = (SVDBVarDeclStmt)child ;
					// Check for members of user defined type (class?) as
					// connected to
					if(childVarDecl.getTypeInfo().getType() == SVDBItemType.TypeInfoUserDef) {
						String typeName = childVarDecl.getTypeName() ;
						if(nodeHash.containsKey(typeName)) {
							DiagConnection con = new DiagConnection("bla", DiagConnectionType.Contains, node, nodeHash.get(typeName)) ;
							model.addConnection(con) ;
							node.addContainedClass(nodeHash.get(typeName)) ;
						}
					}
				}
			}		
		}
		
	}
	
}