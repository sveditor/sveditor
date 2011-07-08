package net.sf.sveditor.core.db.utils;

import java.util.Iterator;

public class SVDBSingleItemIterable<T> implements Iterable<T> {
	private T				fItem;
	
	private class SVDBSingleItemIterator implements Iterator<T> {
		T					fItem;
		int					fIdx = 0;
		
		public SVDBSingleItemIterator(T item) {
			fItem = item;
		}

		@Override
		public boolean hasNext() {
			return (fItem != null && fIdx == 0);
		}

		@Override
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

	@Override
	public Iterator<T> iterator() {
		return new SVDBSingleItemIterator(fItem);
	}

}
