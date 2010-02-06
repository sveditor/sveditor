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
	private SVDBFile		fFile;
	private int				fLine;
	private int				fPos;
	
	public SVDBLocation(SVDBFile file, int line, int pos) {
		fFile = file;
		fLine = line;
		fPos  = pos;
	}

	public SVDBLocation(SVDBLocation other) {
		if (other != null) {
			fFile = other.fFile;
			fLine = other.fLine;
			fPos  = other.fPos;
		}
	}

	public SVDBFile getFile() {
		return fFile;
	}
	
	public int getLine() {
		return fLine;
	}
	
	public int getPos() {
		return fPos;
	}
	
	public void init(SVDBLocation other) {
		fFile = other.fFile;
		fLine = other.fLine;
		fPos  = other.fPos;
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVDBLocation) {
			boolean ret = true;
			SVDBLocation o = (SVDBLocation)other;
			
			if (other == null) {
				return false;
			}
			
			if (o.fFile == null || fFile == null) {
				ret &= o.fFile == fFile;
			} else {
				ret &= o.fFile.equals(fFile);
			}
			
			ret &= (o.fLine == fLine &&	o.fPos == fPos);
			
			return ret;
		}
		return false;
	}
}
