package net.sf.sveditor.core;

public class Tuple<T1, T2> {
	
	private T1				first;
	private T2				second;
	
	public Tuple(T1 it1, T2 it2) {
		first = it1;
		second = it2;
	}
	
	public T1 first() {
		return first;
	}
	
	public T2 second() {
		return second;
	}

}
