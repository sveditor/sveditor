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

import org.sveditor.core.db.SVDBModuleDecl;
import org.sveditor.core.db.index.ISVDBIndex;

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
