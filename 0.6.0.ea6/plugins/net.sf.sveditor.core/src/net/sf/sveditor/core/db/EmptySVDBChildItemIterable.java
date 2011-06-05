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
