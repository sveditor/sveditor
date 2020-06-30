/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.scanutils;

public interface ITextScanner {
	
	int get_ch();
	
	void unget_ch(int ch);
	
	int skipWhite(int ch);
	
	String readIdentifier(int ch);
	
	void startCapture(int ch);
	
	String endCapture();
	
	int skipPastMatch(String pair);
	
	String readString(int ch);
	
	int getLineno();
	
	int getLinepos();
	
	int getFileId();
	
	long getPos();

}
