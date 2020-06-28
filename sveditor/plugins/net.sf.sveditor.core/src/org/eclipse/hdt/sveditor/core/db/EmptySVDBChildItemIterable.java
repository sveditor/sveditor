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


package org.eclipse.hdt.sveditor.core.db;

import java.util.Iterator;

public class EmptySVDBChildItemIterable {
	
	private static final Iterator<ISVDBChildItem> EmptyIterator = new Iterator<ISVDBChildItem>() {

		public boolean hasNext() { return false; }

		public ISVDBChildItem next() { return null; }

		public void remove() { }
	};

	public static final Iterable<ISVDBChildItem> iterable = new Iterable<ISVDBChildItem>() {
		
		public Iterator<ISVDBChildItem> iterator() {
			return EmptyIterator;
		}
	};
}
