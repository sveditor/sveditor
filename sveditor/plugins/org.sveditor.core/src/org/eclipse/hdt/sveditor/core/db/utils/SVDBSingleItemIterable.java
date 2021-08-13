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


package org.sveditor.core.db.utils;

import java.util.Iterator;

public class SVDBSingleItemIterable<T> implements Iterable<T> {
	private T				fItem;
	
	private class SVDBSingleItemIterator implements Iterator<T> {
		T					fItem;
		int					fIdx = 0;
		
		public SVDBSingleItemIterator(T item) {
			fItem = item;
		}

		public boolean hasNext() {
			return (fItem != null && fIdx == 0);
		}

		public T next() {
			if (fIdx == 0) {
				fIdx++;
				return fItem;
			} else {
				return null;
			}
		}

		public void remove() { }
	}
	
	public SVDBSingleItemIterable(T item) {
		fItem = item;
	}

	public Iterator<T> iterator() {
		return new SVDBSingleItemIterator(fItem);
	}

}
