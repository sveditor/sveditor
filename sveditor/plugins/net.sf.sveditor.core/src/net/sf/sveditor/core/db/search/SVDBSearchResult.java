/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
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
