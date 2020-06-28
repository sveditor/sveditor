/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.index.ISVDBIndex;

public class SVDBSearchResult<T> {
	private T						fItem;
	private ISVDBIndex				fIndex;
	
	public SVDBSearchResult(T item, ISVDBIndex index) {
		fItem  = item;
		fIndex = index;
	}
	
	public T getItem() {
		return fItem;
	}
	
	public ISVDBIndex getIndex() {
		return fIndex;
	}

}
