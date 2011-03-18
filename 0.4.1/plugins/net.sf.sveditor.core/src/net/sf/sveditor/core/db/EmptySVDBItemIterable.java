package net.sf.sveditor.core.db;

import java.util.Iterator;

public class EmptySVDBItemIterable {
	
	private static final Iterator<ISVDBItemBase> EmptyIterator = new Iterator<ISVDBItemBase>() {

		public boolean hasNext() { return false; }

		public ISVDBItemBase next() { return null; }

		public void remove() { }
	};

	public static final Iterable<ISVDBItemBase> iterable = new Iterable<ISVDBItemBase>() {
		
		public Iterator<ISVDBItemBase> iterator() {
			return EmptyIterator;
		}
	};
}
