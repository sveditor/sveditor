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

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBLocation;

/**
 * Reference matcher driven by a reference finder. The task of 
 * this class is to match references found by the finder against
 * the spec.
 * 
 * @author ballance
 *
 */
public class SVDBRefMatcher implements ISVDBRefFinderVisitor {
	private ISVDBRefSearchSpec		fRefSpec;
	/*
	private SVDBRefType				fRefType;
	private String					fRefName;
	 */
	ISVDBRefVisitor					fRefCollector;
	
	public SVDBRefMatcher(
			ISVDBRefSearchSpec	ref_spec,
			ISVDBRefVisitor		ref_visitor) {
		fRefSpec = ref_spec;
		fRefCollector = ref_visitor;
	}

	/*
	public SVDBRefMatcher(
			SVDBRefType			ref_type,
			String				ref_name,
			ISVDBRefVisitor		ref_visitor) {
		fRefType = ref_type;
		fRefName = ref_name;
	}
	 */
	
	/*
	public List<SVDBRefItem> find_refs(SVDBFile file) {
		visitFile(file);
		return fRefList;
	}
	 */

	public void visitRef(
			long		 			loc,
			SVDBRefType 			type,
			Stack<ISVDBItemBase>	scope,
			String 					name) {
		if (fRefSpec.matches(loc, type, scope, name)) {
			List<ISVDBItemBase> ref_path = new ArrayList<ISVDBItemBase>();
			ref_path.addAll(scope);
			SVDBRefItem ref = new SVDBRefItem(ref_path, name, type);
			fRefCollector.visitRef(fRefSpec, ref);
		}
	}
}
