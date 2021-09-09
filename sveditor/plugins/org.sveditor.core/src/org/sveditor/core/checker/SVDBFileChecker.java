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
package org.sveditor.core.checker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.sveditor.core.db.ISVDBChildParent;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.ISVDBScopeItem;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.index.ISVDBMarkerMgr;
import org.sveditor.core.preproc.ISVPreProcFileMapper;

public class SVDBFileChecker implements ISVDBChecker, ISVDBCheckErrorReporter {
	private ISVDBMarkerMgr								fMarkerMgr;
	private ISVPreProcFileMapper						fMapper;
	private Map<SVDBItemType, List<ISVDBCheckVisitor>> 	fCheckers;
	
	public SVDBFileChecker(ISVDBMarkerMgr marker_mgr, ISVPreProcFileMapper mapper) {
		fMarkerMgr = marker_mgr;
		fMapper = mapper;
		fCheckers = new HashMap<SVDBItemType, List<ISVDBCheckVisitor>>();
	}
	
	public void addChecker(SVDBItemType t, ISVDBCheckVisitor v) {
		if (!fCheckers.containsKey(t)) {
			fCheckers.put(t, new ArrayList<ISVDBCheckVisitor>());
		}
		List<ISVDBCheckVisitor> visitors = fCheckers.get(t);
	
		if (!visitors.contains(v)) {
			visitors.add(v);
		}
	}
	
	public void check(ISVDBScopeItem scope) {
		List<ISVDBCheckVisitor> v_l;
		
		if ((v_l = fCheckers.get(scope.getType())) != null) {
			for (ISVDBCheckVisitor v : v_l) {
				v.visit(this, scope);
			}
		}
		
		// Now, traverse through the sub-scopes
		for (ISVDBItemBase it : scope.getChildren()) {
			check(it);
		}
	}
	
	private void check(ISVDBItemBase it) {
		List<ISVDBCheckVisitor> v_l;
		
		if ((v_l = fCheckers.get(it.getType())) != null) {
			for (ISVDBCheckVisitor v : v_l) {
				v.visit(this, it);
			}
		}

		if (it instanceof ISVDBChildParent) {
			for (ISVDBItemBase it_c : ((ISVDBChildParent)it).getChildren()) {
				check(it_c);
			}
		}
	}

	@Override
	public void error(SVDBLocation loc, String msg) {
		String file = null;
		if (fMapper != null && loc != null) {
			file = fMapper.mapFileIdToPath(loc.getFileId());
		}
		
		if (file != null) {
			fMarkerMgr.addMarker(file, 
					ISVDBMarkerMgr.MARKER_TYPE_ERROR, loc.getLine(), msg);
		}
	}
	
}
