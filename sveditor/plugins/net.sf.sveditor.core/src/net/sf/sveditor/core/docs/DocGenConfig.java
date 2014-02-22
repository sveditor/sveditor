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
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class DocGenConfig {
	
	private Map<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPkgSet ;

	private File 										outputDir ;
	private boolean 									includeUndocumentedPkgsInPkgIndex = true ;

	
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
