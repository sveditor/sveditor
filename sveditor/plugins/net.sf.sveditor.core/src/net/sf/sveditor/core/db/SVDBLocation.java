/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
	private long			fLocation;

	public SVDBLocation(int file_id, int line, int pos) {
		fLocation = pack(file_id, line, pos);
	}
	
	public SVDBLocation(long location) {
		fLocation = location;
	}

	public SVDBLocation(SVDBLocation other) {
		fLocation = other.fLocation;
	}
	
	public int getFileId() {
		return unpackFileId(fLocation);
	}

	public int getLine() {
		return unpackLineno(fLocation);
	}
	
	public int getPos() {
		return unpackPos(fLocation);
	}
	
	public void init(SVDBLocation other) {
		fLocation = other.fLocation;
	}
	
	public SVDBLocation duplicate() {
		return new SVDBLocation(this);
	}
	
	public boolean equals(Object other) {
		if (other instanceof SVDBLocation) {
			boolean ret = true;
			SVDBLocation o = (SVDBLocation)other;
			
			ret &= (o.fLocation == fLocation);
			
			return ret;
		}
		return false;
	}
	
	public String toString() {
		return "" + unpackFileId(fLocation) + ":" + 
					unpackLineno(fLocation) + ":" +
					unpackPos(fLocation);
	}
	
	public static String toString(long location) {
		return "TODO: " + location;
	}
	
	public static long pack(int fileid, int lineno, int linepos) {
		long ret = fileid;
		ret <<= 32;
		ret |= (lineno & 0xFFFFFF) << 8;
		ret |= linepos;
		
		return ret;
	}
	
	public static int unpackFileId(long location) {
		return (int)((location >> 32) & 0xFFFFFFFF);
	}
	
	public static int unpackLineno(long location) {
		int ret = (int)((location >> 8) & 0xFFFFFF);
		return (ret == 0xFFFFFF)?-1:ret;
	}
	
	public static int unpackPos(long location) {
		int ret = (int)(location & 0xFF);
		return (ret == 0xFF)?-1:ret;
	}
}
