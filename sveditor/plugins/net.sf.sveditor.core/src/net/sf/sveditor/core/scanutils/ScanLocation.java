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


package net.sf.sveditor.core.scanutils;


public class ScanLocation implements IScanLocation {
	private String			fFile;
	private int				fFileId;
	private int				fLineno;
	private int				fLinepos;
	
	public ScanLocation(String file, int lineno, int linepos) {
		fFile = file;
		fLineno = lineno;
		fLinepos = linepos;
	}
	
	public ScanLocation(int file_id, int lineno, int linepos) {
		fFileId  = file_id;
		fLineno  = lineno;
		fLinepos = linepos;
	}
	
	public String getFileName() {
		return fFile;
	}
	
	public void setFileName(String name) {
		fFile = name;
	}
	
	public int getFileId() {
		return fFileId;
	}
	
	public int getLineNo() {
		return fLineno;
	}
	
	public void setLineNo(int num) {
		fLineno = num;
	}
	
	public int getLinePos() {
		return fLinepos;
	}
	
	public void setLinePos(int pos) {
		fLinepos = pos;
	}
}
