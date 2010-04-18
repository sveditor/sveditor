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


package net.sf.sveditor.core.parser;

import java.io.IOException;
import java.io.InputStream;

public class SVInputStream_sav {
	private SystemVerilogParser_sav 			fParser;
	private int								fLineno;
	private int								fLinepos;
	private InputStream						fInput;
	private StringBuffer					fUngetBuffer;
	
	public SVInputStream_sav(InputStream in) {
		fInput = in;
		fUngetBuffer = new StringBuffer();
	}
	
	public void init(SystemVerilogParser_sav p) {
		fParser = p;
	}
	
	public int get_ch() {
		int ch = -1;
		
		if (fUngetBuffer.length() > 0) {
			ch = fUngetBuffer.charAt(fUngetBuffer.length()-1);
			fUngetBuffer.setLength(fUngetBuffer.length()-1);
		} else {
			try {
				ch = fInput.read(); 
			} catch (IOException e) {
			}
		}
		
		return ch;
	}
	
	public void unget_ch(int ch) {
		if (ch != -1) {
			fUngetBuffer.append((char)ch);
		}
	}

}
