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


package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBChildParent extends SVDBChildItem implements ISVDBChildParent {
	private List<ISVDBChildItem>			fItems;
	
	public SVDBChildParent(SVDBItemType type) {
		super(type);
		fItems = new ArrayList<ISVDBChildItem>();
	}

	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fItems.add(item);
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return new Iterable<ISVDBChildItem>() {
			public Iterator<ISVDBChildItem> iterator() {
				return fItems.iterator();
			}
		};
	}

}
