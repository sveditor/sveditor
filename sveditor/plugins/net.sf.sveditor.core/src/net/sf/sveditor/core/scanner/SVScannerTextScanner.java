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


package net.sf.sveditor.core.scanner;

import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVScannerTextScanner extends AbstractTextScanner {
	private SVPreProcScanner			fScanner;
	private StringBuffer				fUngetStr;
	private long						fPos;
	
	public SVScannerTextScanner(SVPreProcScanner scanner) {
		super();
		fScanner        = scanner;
		fUngetStr       = new StringBuffer();
		fPos			= 1;
	}
	
	public int get_ch() {
		int ch = -1;
		
		if (fUngetStr.length() > 0) {
			ch = fUngetStr.charAt(fUngetStr.length()-1);
			fUngetStr.setLength(fUngetStr.length()-1);
		} else {
			ch = fScanner.get_ch();
		}

		if (ch != -1 && fCaptureEnabled) {
			fCaptureBuffer.append((char)ch);
		}
		
		fPos++;
		
		return ch;
	}
	
	public void unget_ch(int ch) {
		fUngetStr.append((char)ch);
		fPos--;
	}
	

	public int skipPastMatch(String pair, String escape) {
		int begin = pair.charAt(0);
		int end = pair.charAt(1);
		int matchLevel = 1;
		int ch;
		
		do {
			ch = get_ch();
			if (ch == begin) {
				matchLevel++;
			} else if (ch == end) {
				matchLevel--;
			} else {
				boolean do_escape = false;
				for (int i=0; i<escape.length(); i++) {
					if (ch == escape.charAt(i)) {
						do_escape = true;
						break;
					}
				}
				if (do_escape) {
					unget_ch(ch);
					break;
				}
			}
		} while (matchLevel > 0 && ch != -1);
		
		return get_ch();
	}
	
	public void unget_str(String str) {
		for (int i=str.length()-1; i>=0; i--) {
			fUngetStr.append(str.charAt(i));
			fPos--;
		}
	}
	
	public ScanLocation getLocation() {
		return fScanner.getLocation();
	}
	
	public long getPos() {
		return fPos;
	}
}
