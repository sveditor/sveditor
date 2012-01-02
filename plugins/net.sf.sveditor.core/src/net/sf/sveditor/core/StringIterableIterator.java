package net.sf.sveditor.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class StringIterableIterator implements Iterable<String>,
		Iterator<String> {
	private List<Iterable<String>>			fIterables;
	private int								fIterableIdx;
	private Iterator<String>				fIterator;
	
	public StringIterableIterator() {
		fIterables = new ArrayList<Iterable<String>>();
	}

	private StringIterableIterator(List<Iterable<String>> it) {
		fIterables = new ArrayList<Iterable<String>>();
		fIterables.addAll(it);
	}

	public void addIterable(Iterable<String> it) {
		fIterables.add(it);
	}

	public boolean hasNext() {
		if (fIterator == null || !fIterator.hasNext()) {
			fIterator = null;
			while (fIterableIdx < fIterables.size()) {
				fIterator = fIterables.get(fIterableIdx).iterator();
				fIterableIdx++;
				if (fIterator.hasNext()) {
					break;
				}
				fIterator = null;
			}
		}
		
		return (fIterator != null && fIterator.hasNext());
	}

	public String next() {
		if (hasNext()) {
			return fIterator.next();
		} else {
			return null;
		}
	}

	public void remove() {
		// Ignored
		throw new RuntimeException("Elements cannot be removed from StringIterableIterator");
	}

	public Iterator<String> iterator() {
		return new StringIterableIterator(fIterables);
	}

}
