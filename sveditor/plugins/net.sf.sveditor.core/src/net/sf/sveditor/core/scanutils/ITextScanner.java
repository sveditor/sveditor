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

public interface ITextScanner {
	
	int get_ch();
	
	void unget_ch(int ch);
	
	int skipWhite(int ch);
	
	String readIdentifier(int ch);
	
	void startCapture(int ch);
	
	String endCapture();
	
	int skipPastMatch(String pair);
	
	String readString(int ch);
	
	ScanLocation getLocation();
	
	long getPos();

}
