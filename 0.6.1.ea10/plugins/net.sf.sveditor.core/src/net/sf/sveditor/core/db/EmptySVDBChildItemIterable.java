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
