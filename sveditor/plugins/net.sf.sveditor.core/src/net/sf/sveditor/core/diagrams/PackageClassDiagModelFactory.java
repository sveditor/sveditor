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

import java.util.List;

import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindPackageDefaultNameMatcher;

import org.eclipse.core.runtime.NullProgressMonitor;

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
