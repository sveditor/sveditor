/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.refs;

import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBLocation;

public class SVDBFileRefCollector implements ISVDBRefFinderVisitor {
	private SVDBRefCacheEntry			fReferences;
	
	public SVDBFileRefCollector() {
		fReferences = new SVDBRefCacheEntry();
	}

	/*
	public Set<RefType> getRefTypeSet() {
		return fReferences.keySet();
	}
	
	public Set<String> getRefSet(RefType type) {
		return fReferences.get(type);
	}
	 */
	
	public SVDBRefCacheEntry getReferences() {
		return fReferences;
	}

	public void visitRef(
			SVDBLocation 			loc, 
			SVDBRefType 			type, 
			Stack<ISVDBChildItem>	scope_stack,
			String 					name) {
		switch (type) {
			case FieldReference: {
				fReferences.addFieldRef(name);
			} break;
			case ImportReference: {
				fReferences.addImportRef(name);
			} break;
			case IncludeReference: {
				fReferences.addIncludeRef(name);
			} break;
			case TypeReference: {
				fReferences.addTypeRef(name);
			} break;
		}
	}
}
