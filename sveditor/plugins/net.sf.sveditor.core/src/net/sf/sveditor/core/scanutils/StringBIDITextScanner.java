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

import java.util.ArrayList;
import java.util.List;

public class StringBIDITextScanner 
	extends AbstractTextScanner implements IBIDITextScanner {
	private String				fData;
	private int				fIdx;
	private int				fUngetCh;
	List<Integer>				fLineOffsets;
	
	public StringBIDITextScanner(String data) {
		fData    = data;
		fIdx     = 0;
		fUngetCh = -1;
		
		fLineOffsets = new ArrayList<Integer>();
		fLineOffsets.add(0);
		
		for (int i=0; i<fData.length(); i++) {
			if (fData.charAt(i) == '\n') {
				fLineOffsets.add(i+1);
			}
		}
	}

	public void setScanFwd(boolean scanFwd) {
		if (fScanFwd != scanFwd) {
			fUngetCh = -1;
		}
		fScanFwd = scanFwd;
	}

	public int get_ch() {
		int ret = -1;
		
		if (fUngetCh != -1) {
			ret = fUngetCh;
			fUngetCh = -1;
		} else {
			if (fScanFwd) {
				if (fIdx < fData.length()) {
					ret = fData.charAt(fIdx);
					fIdx++;
				}
			} else {
				if (fIdx >= 0 && fData.length() > 0) {
					if (fIdx >= fData.length()) {
						fIdx = fData.length()-1;
					}
					ret = fData.charAt(fIdx);
					fIdx--;
				}
			}
		}

		return ret;
	}

	public ScanLocation getLocation() {
		int lineno = -1;
		int linepos = -1;
		
		for (int i=0; i<fLineOffsets.size(); i++) {
			int pos = fLineOffsets.get(i);
			if (fIdx <= pos) {
				lineno = i;
				linepos = pos; // 
				break;
			}
		}
		
		return new ScanLocation("", lineno, linepos);
	}

	public void unget_ch(int ch) {
		if (ch != -1) {
			if (fScanFwd) {
				fIdx--;
			} else {
				fIdx++;
			}
		}
	}

	public String get_str(long start, int length) {
		return fData.substring((int)start, (int)start+length);
	}

	public long getPos() {
		return fIdx;
	}

	public void seek(long pos) {
		fIdx = (int)pos;
	}
	
	public String getContent() {
		return fData;
	}

	
}
