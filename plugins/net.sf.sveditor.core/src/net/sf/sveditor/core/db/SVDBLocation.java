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


package net.sf.sveditor.core.db;

public class SVDBLocation {
	private int				fLine;
	private int				fPos;

	/*
	public SVDBLocation(int line) {
		fLine = line;
		fPos  = -1;
	}
	 */

	public SVDBLocation(int line, int pos) {
		fLine = line;
		fPos  = pos;
	}

	public SVDBLocation(SVDBLocation other) {
		fLine = other.fLine;
		fPos  = other.fPos;
	}

	public int getLine() {
		return fLine;
	}
	
	public int getPos() {
		return fPos;
	}
	
	public void init(SVDBLocation other) {
		fLine = other.fLine;
		fPos  = other.fPos;
	}
	
	public SVDBLocation duplicate() {
		return new SVDBLocation(this);
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVDBLocation) {
			boolean ret = true;
			SVDBLocation o = (SVDBLocation)other;
			
			ret &= (o.fLine == fLine &&	o.fPos == fPos);
			
			return ret;
		}
		return false;
	}
}
