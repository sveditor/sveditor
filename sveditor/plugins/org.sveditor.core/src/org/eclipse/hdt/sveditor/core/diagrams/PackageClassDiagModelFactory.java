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

package org.eclipse.hdt.sveditor.core.diagrams;

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBPackageDecl;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindPackageDefaultNameMatcher;

public class PackageClassDiagModelFactory extends AbstractDiagModelFactory {
	
	private SVDBPackageDecl fPackageDecl ;
	
	public PackageClassDiagModelFactory(ISVDBIndex index, SVDBPackageDecl pkgDecl) {
		super(index) ;
		fPackageDecl = pkgDecl ;
	}

	public DiagModel build() {
		
		DiagModel model = new DiagModel() ;
		
		List<SVDBDeclCacheItem> pkgDeclItems 
			= fIndex.findGlobalScopeDecl(new NullProgressMonitor(), 
					fPackageDecl.getName(), 
					new SVDBFindPackageDefaultNameMatcher()) ;
		
		if(pkgDeclItems.size() == 0) {
			return null ;
		}
		
		SVDBDeclCacheItem pkgDeclItem = pkgDeclItems.get(0) ;
		
		List<SVDBDeclCacheItem> pkgDecls = fIndex.findPackageDecl(new NullProgressMonitor(), pkgDeclItem) ; 
		if(pkgDecls != null) {
			for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
				if(pkgDecl.getType() == SVDBItemType.ClassDecl) {
					createNodeForClass(model, (SVDBClassDecl)pkgDecl.getSVDBItem()) ;
				}
				}
			}
		
			createConnectionsForNodes(model, model.getNodes()) ;
		
		return model ;
		
	}	

}
