/****************************************************************************

 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial contributor 
 ****************************************************************************/

package net.sf.sveditor.core.diagrams;

import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.index.ISVDBIndex;

public class ModuleDiagModelFactory extends AbstractDiagModelFactory {
	
	private SVDBModuleDecl fModuleDecl ;
	
	public ModuleDiagModelFactory(ISVDBIndex index, SVDBModuleDecl moduleDecl) {
		super(index);
		fModuleDecl = moduleDecl;
	}

	public DiagModel build() {
		DiagModel model = new DiagModel() ;
		
		if(fModuleDecl != null) {
			
			DiagNode moduleNode = createNodeForModule(model, fModuleDecl);
			
			// Check for a super class
			//
			/*
			if(fClassDecl.getSuperClass() != null) {
				DiagNode superNode = null ;
				String superName = fClassDecl.getSuperClass().getName() ;
				superNode = model.getVisitedClass(superName) ;
				if(superNode == null) {
					SVDBFindSuperClass super_finder = new SVDBFindSuperClass(fIndex) ;
					ISVDBChildParent si = super_finder.find(fClassDecl);
					if(si != null && si.getType() == SVDBItemType.ClassDecl) {
						superNode = createNodeForClass(model, (SVDBClassDecl)si) ;
					}
				}
				if(superNode != null) {
					DiagConnection con = new DiagConnection("bla", DiagConnectionType.Inherits, moduleNode, superNode) ;
					model.addConnection(con) ;
					moduleNode.addSuperClass(superNode) ;
				}
			}
			 */
			
			createNodesAndConnectionsForContainedModules(model, moduleNode) ;
		}		
		
		return model ;
		
	}	

}
