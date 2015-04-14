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
	public int				fFileId;
	public int				fLine;
	public int				fPos;

	/*
	public SVDBLocation(int line, int pos) {
		fFileId = -1;
		fLine   = line;
		fPos    = pos;
	}
	 */
	
	public SVDBLocation(int file_id, int line, int pos) {
		fFileId = file_id;
		fLine   = line;
		fPos    = pos;
	}
	
	public SVDBLocation(long location) {
		// TODO: unpack
		fFileId = unpackFileId(location);
		fLine = unpackLineno(location);
		fPos = unpackPos(location);
	}

	public SVDBLocation(SVDBLocation other) {
		fFileId = other.fFileId;
		fLine	= other.fLine;
		fPos	= other.fPos;
	}
	
	public int getFileId() {
		return fFileId;
	}

	public int getLine() {
		return fLine;
	}
	
	public int getPos() {
		return fPos;
	}
	
	public void init(SVDBLocation other) {
		fFileId = other.fFileId;
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
			
			ret &= (o.fLine == fLine &&	o.fPos == fPos && o.fFileId == fFileId);
			
			return ret;
		}
		return false;
	}
	
	public String toString() {
		return fFileId + ":" + fLine;
	}
	
	public static String toString(long location) {
		return "TODO: " + location;
	}
	
	public static long pack(int fileid, int lineno, int linepos) {
		long ret = (fileid << 32);
		ret |= (lineno & 0xFFFFFF) << 8;
		ret |= linepos;
		
		return ret;
	}
	
	public static int unpackFileId(long location) {
		return (int)((location >> 32) & 0xFFFFFFFF);
	}
	
	public static int unpackLineno(long location) {
		return (int)((location >> 8) & 0xFFFFFF);
	}
	
	public static int unpackPos(long location) {
		return (int)(location & 0xFF);
	}
}
