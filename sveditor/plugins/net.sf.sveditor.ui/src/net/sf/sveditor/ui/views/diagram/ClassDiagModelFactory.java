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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.diagrams.DiagConnection;
import net.sf.sveditor.core.diagrams.DiagConnectionType;
import net.sf.sveditor.core.diagrams.DiagNode;

/*
 * TODO: this model needs a lot of work.  just the bare bones to inefficiently create a diagram for a single class
 */

public class ClassDiagModelFactory extends AbstractDiagModelFactory {
	
	private SVDBClassDecl fClassDecl ;
	
	public ClassDiagModelFactory(List<ISVDBIndex> projectIndexList, SVDBClassDecl classDecl) {
		super(projectIndexList) ;
		fClassDecl = classDecl ;
	}

	@Override
	public DiagModel build() {
		DiagModel model = new DiagModel() ;
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
				
		fProjectIndexList =	rgy.getAllProjectLists() ;
		
		if(fClassDecl != null) {
			
			DiagNode classNode = createNodeForClass(model, fClassDecl) ;
			
			// Check for a super class
			//
			if(fClassDecl.getSuperClass() != null) {
				DiagNode superNode = null ;
				String superName = fClassDecl.getSuperClass().getName() ;
				superNode = model.getVisitedClass(superName) ;
				if(superNode == null) {
					for(ISVDBIndex svdbIndex: fProjectIndexList) {
						SVDBFindSuperClass super_finder = new SVDBFindSuperClass(svdbIndex) ;
						ISVDBChildParent si = super_finder.find(fClassDecl);
						if(si != null && si.getType() == SVDBItemType.ClassDecl) {
							superNode = createNodeForClass(model, (SVDBClassDecl)si) ;
							break ;
						}
					}				
				}
				if(superNode != null) {
					DiagConnection con = new DiagConnection("bla", DiagConnectionType.Inherits, classNode, superNode) ;
					model.addConnection(con) ;
					classNode.addSuperClass(superNode) ;
				}
			}
			
			// 
			
			createNodesAndConnectionsForContainedClasses(model, classNode) ;
		}		
		
		return model ;
		
	}	

}
