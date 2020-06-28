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

import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;

public class ClassDiagModelFactory extends AbstractDiagModelFactory {
	
	private SVDBClassDecl fClassDecl ;
	
	public ClassDiagModelFactory(ISVDBIndex index, SVDBClassDecl classDecl) {
		super(index) ;
		fClassDecl = classDecl ;
	}

	public DiagModel build() {
		DiagModel model = new DiagModel() ;
		
		if(fClassDecl != null) {
			
			DiagNode classNode = createNodeForClass(model, fClassDecl) ;
			
			// Check for a super class
			//
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
