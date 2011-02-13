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

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBLocation {
	private int				fLine;
	private int				fPos;

	/*
	public SVDBLocation(int line) {
		fLine = line;
		fPos  = -1;
	}
	 */
	
	public static SVDBLocation readLocation(IDBReader reader) throws DBFormatException {
		int line = reader.readInt();
		int pos = reader.readInt();
		
		if (line == -1 && pos == -1) {
			return null;
		} else {
			return new SVDBLocation(line, pos);
		}
	}
	
	public static void writeLocation(SVDBLocation loc, IDBWriter writer) {
		if (loc == null) {
			writer.writeInt(-1);
			writer.writeInt(-1);
		} else {
			writer.writeInt(loc.getLine());
			writer.writeInt(loc.getPos());
		}
	}

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
