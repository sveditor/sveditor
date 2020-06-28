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
package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFileTree;

/**
 * Provides a path to a given file, listing include locations, etc
 * 
 * @author ballance
 *
 */
public class SVDBFilePath {
	
	private List<Tuple<SVDBFileTree, ISVDBItemBase>>		fFilePath;
	
	public SVDBFilePath() {
		fFilePath = new ArrayList<Tuple<SVDBFileTree,ISVDBItemBase>>();
	}
	
	public void addPath(SVDBFileTree ft, ISVDBItemBase item) {
		fFilePath.add(new Tuple<SVDBFileTree, ISVDBItemBase>(ft, item));
	}
	
	public List<Tuple<SVDBFileTree, ISVDBItemBase>> getPath() {
		return fFilePath;
	}

}
