/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.db.refs;

import java.util.HashSet;
import java.util.Set;

import org.sveditor.core.db.attr.SVDBDoNotSaveAttr;

public class SVDBRefCacheEntry {
	
	@SVDBDoNotSaveAttr
	private String				fFileName;
	
	public Set<String>			fTypeReferences;
	public Set<String>			fFieldReferences;
	public Set<String>			fImportReferences;
	public Set<String>			fIncludeReferences;
	
	public SVDBRefCacheEntry() {
		fTypeReferences = new HashSet<String>();
		fFieldReferences = new HashSet<String>();
		fImportReferences = new HashSet<String>();
		fIncludeReferences = new HashSet<String>();
	}

	public Set<String> getRefSet(SVDBRefType t) {
		switch (t) {
			case FieldReference: return fFieldReferences;
			case ImportReference: return fImportReferences;
			case IncludeReference: return fIncludeReferences;
			case TypeReference: return fTypeReferences;
		}
		return null;
	}
	
	public void addFieldRef(String name) {
		if (!fFieldReferences.contains(name)) {
			fFieldReferences.add(name);
		}
	}
	
	public void addImportRef(String name) {
		if (!fImportReferences.contains(name)) {
			fImportReferences.add(name);
		}
	}
	
	public void addIncludeRef(String name) {
		if (!fIncludeReferences.contains(name)) {
			fIncludeReferences.add(name);
		}
	}
	
	public void addTypeRef(String name) {
		if (!fTypeReferences.contains(name)) {
			fTypeReferences.add(name);
		}
	}

	public void setFilename(String filename) {
		fFileName = filename;
	}
	
	public String getFilename() {
		return fFileName;
	}
}
