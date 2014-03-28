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


package net.sf.sveditor.core.scanutils;

import java.io.IOException;
import java.io.InputStream;

public class InputStreamTextScanner extends AbstractTextScanner {
	private InputStream					fInput;
	private String						fFilename;
	private int							fUngetCh;
	private byte						fBuffer[];
	private int							fBufferIdx;
	private int							fBufferMax;
	private long						fPos;
	
	public InputStreamTextScanner(InputStream in, String filename) {
		super();
		
		fInput    = in;
		fFilename = filename;
		fUngetCh  = -1;
		fBuffer   = new byte[1024*64]; // 64K buffer
		fBufferIdx = 0;
		fBufferMax = 0;
		fPos       = 1;
	}

	public ScanLocation getLocation() {
		return new ScanLocation(fFilename, fLineno, fLinepos);
	}
	
	public int get_ch() {
		int ch = -1;
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
			fPos++;
			return ch;
		}

		if (fBufferIdx >= fBufferMax) {
			fBufferIdx = 0;
			fBufferMax = 0;
			try {
				fBufferMax = fInput.read(fBuffer, 0, fBuffer.length);
			} catch (IOException e) {}
		}
		
		if (fBufferIdx < fBufferMax) {
			ch = fBuffer[fBufferIdx++];
		}

		fLinepos++;
		if (fLastCh == '\n') {
			fLineno++;
			fLinepos = 0;
		}
		fLastCh = ch;
		
		fPos++;
		
		return ch;
	}

	public void unget_ch(int ch) {
		fUngetCh = ch;
		
		if (fUngetCh != -1) {
			fPos--;
		}
	}
	
	public long getPos() {
		return fPos;
	}
}
