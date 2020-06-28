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

public class SVDBIndexChangeEvent {
	public enum Type {
		FullRebuild,
		IncrRebuild
	};
	
	private Type						fType;
	private List<SVDBIndexChangeDelta>	fDeltaList;
	private ISVDBIndex					fIndex;
	
	public SVDBIndexChangeEvent(Type type, ISVDBIndex index) {
		fType = type;
		fIndex = index;
		fDeltaList = new ArrayList<SVDBIndexChangeDelta>();
	}
	
	public Type getType() { return fType; }
	
	public ISVDBIndex getIndex() { return fIndex; }
	
	public void addDelta(SVDBIndexChangeDelta d) {
		fDeltaList.add(d);
	}
	
	public List<SVDBIndexChangeDelta> getDeltaList() {
		return fDeltaList;
	}

}
