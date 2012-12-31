/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


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
	
	public void setFirst(T1 f) {
		first = f;
	}
	
	public T2 second() {
		return second;
	}
	
	public void setSecond(T2 s) {
		second = s;
	}
	
	@SuppressWarnings("unchecked")
	public boolean equals(Object obj) {
		if (obj instanceof Tuple) {
			Tuple<T1, T2> t = (Tuple<T1, T2>)obj;
			boolean eq = true;
			
			if (t.first == null || first == null) {
				eq &= (t.first == first);
			} else {
				eq &= t.first.equals(first);
			}
			if (t.second == null || second == null) {
				eq &= (t.second == second);
			} else {
				eq &= t.second.equals(second);
			}
			return eq;
		} else {
			return super.equals(obj);
		}
	}

}
