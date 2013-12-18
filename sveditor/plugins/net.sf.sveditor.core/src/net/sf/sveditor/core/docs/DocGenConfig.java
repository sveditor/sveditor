/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs;

import java.io.File;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class DocGenConfig {
	
	private Set<Tuple<SVDBDeclCacheItem,ISVDBIndex>> 	fPackages ;
	private Set<SVDBDeclCacheItem>						fModulePrograms;
	private File 										outputDir ;
	private boolean 									includeUndocumentedPkgsInPkgIndex = true ;

	public Set<Tuple<SVDBDeclCacheItem,ISVDBIndex>> getSelectedPackages() {
		return fPackages;
	}
	public void setSelectedPackages(Set<Tuple<SVDBDeclCacheItem,ISVDBIndex>> fPackages) {
		this.fPackages = fPackages ;
	}
	
	public void setModulePrograms(Set<SVDBDeclCacheItem> mod_programs) {
		fModulePrograms = mod_programs;
	}
	
	public Set<SVDBDeclCacheItem> getModulePrograms() {
		return fModulePrograms;
	}
	
	public void setOutputDir(File outputDir) {
		this.outputDir = outputDir ;
	}
	public File getOutputDir() {
		return outputDir ;
	}
	
	public boolean getIncludeUndocumentedPkgsInPkgIndex() {
		return includeUndocumentedPkgsInPkgIndex;
	}
	public void setIncludeUndocumentedPkgsInPkgIndex(
			boolean includeUndocumentedPkgsInPkgIndex) {
		this.includeUndocumentedPkgsInPkgIndex = includeUndocumentedPkgsInPkgIndex;
	}

}
