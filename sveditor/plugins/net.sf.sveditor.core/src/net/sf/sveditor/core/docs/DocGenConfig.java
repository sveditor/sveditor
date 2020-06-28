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
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs;

import java.io.File;
import java.util.Map;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class DocGenConfig {
	
	private Map<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPkgSet ;

	private File 										outputDir ;

	private boolean 									includeUndocumentedPkgsInPkgIndex = true ;

	public boolean	fPackagesSelected = false ;
	
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
	public Map<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem, ISVDBIndex>> getPkgSet() {
		return fPkgSet;
	}
	public void setPkgSet(Map<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem, ISVDBIndex>> map) {
		this.fPkgSet = map;
	}

}
