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

import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class DocGenConfig {
	
	private Set<SVDBDeclCacheItem> fPackages ;
	private File outputDir ;

	public Set<SVDBDeclCacheItem> getSelectedPackages() {
		return fPackages;
	}
	public void setSelectedPackages(Set<SVDBDeclCacheItem> fPackages) {
		this.fPackages = fPackages ;
	}
	
	public void setOutputDir(File outputDir) {
		this.outputDir = outputDir ;
	}
	public File getOutputDir() {
		return outputDir ;
	}

}
