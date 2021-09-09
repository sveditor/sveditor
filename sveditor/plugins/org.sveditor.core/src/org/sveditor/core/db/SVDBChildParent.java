/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.core.db;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class SVDBChildParent extends SVDBChildItem implements ISVDBChildParent {
	public List<ISVDBChildItem>			fItems;
	
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
