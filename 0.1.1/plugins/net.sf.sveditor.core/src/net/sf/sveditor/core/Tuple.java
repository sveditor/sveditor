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
	
	public T2 second() {
		return second;
	}

}
