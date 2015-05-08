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

import net.sf.sveditor.core.db.ISVDBItemBase;
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

	public Map<String, List<Integer>> getReferences() {
		return fReferences;
	}

	public void visitRef(
			long 					loc,
			SVDBRefType 			type,
			Stack<ISVDBItemBase>	scope_stack,
			String 					name) {
		
//		System.out.println("visitRef: " + loc + " " + type + " " + name);
		
		if (loc == -1) {
			// Step up the stack to find the last location
			for (int i=scope_stack.size()-1; i>=0; i--) {
				if (scope_stack.get(i).getLocation() != -1) {
					loc = scope_stack.get(i).getLocation();
					break;
				}
			}
		}
		
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
	
	private void addRef(long loc, String name) {
//		System.out.println("addRef: " + loc + " " + name);
		if (loc != -1) {
			int file_id = SVDBLocation.unpackFileId(loc);
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
