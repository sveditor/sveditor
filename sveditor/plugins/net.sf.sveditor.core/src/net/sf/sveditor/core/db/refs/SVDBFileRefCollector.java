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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBLocation;

/**
 * Builds an index of the identifier references present in a given
 * file
 * 
 * @author ballance
 *
 */
public class SVDBFileRefCollector implements ISVDBRefFinderVisitor {
	private Map<String, List<Integer>>	fReferences;
	
	public SVDBFileRefCollector() {
		this(null);
	}
	
	public SVDBFileRefCollector(Map<String, List<Integer>> ref_map) {
		if (ref_map == null) {
			ref_map = new HashMap<String, List<Integer>>();
		}
		fReferences = ref_map;
	}

	/*
	public Set<RefType> getRefTypeSet() {
		return fReferences.keySet();
	}
	
	public Set<String> getRefSet(RefType type) {
		return fReferences.get(type);
	}
	 */
	
	public Map<String, List<Integer>> getReferences() {
		return fReferences;
	}

	public void visitRef(
			SVDBLocation 			loc,
			SVDBRefType 			type,
			Stack<ISVDBChildItem>	scope_stack,
			String 					name) {
		switch (type) {
			case FieldReference: {
				addRef(loc, name);
			} break;
			case ImportReference: {
				addRef(loc, name);
			} break;
			case IncludeReference: {
				addRef(loc, name);
			} break;
			case TypeReference: {
				addRef(loc, name);
			} break;
		}
	}
	
	private void addRef(SVDBLocation loc, String name) {
		if (loc != null) {
			int file_id = loc.getFileId();
			List<Integer> file_list = fReferences.get(name);

			if (file_list == null) {
				file_list = new ArrayList<Integer>();
				fReferences.put(name, file_list);
			}

			if (!file_list.contains(file_id)) {
				file_list.add(file_id);
			}
		}
	}
}
