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

import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.diagrams.DiagConnection;
import net.sf.sveditor.core.diagrams.DiagConnectionType;
import net.sf.sveditor.core.diagrams.DiagNode;

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
