/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.argfile.parser;

import java.util.List;

import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.scanutils.AbstractTextScanner;
import org.sveditor.core.scanutils.ScanLocation;

public class SVArgFilePreProcOutput extends AbstractTextScanner {
	private StringBuilder				fText;
	private List<Integer>				fLineMap;
	private int						fLineIdx;
	private int						fNextLinePos;
	private int						fIdx;
	private int						fUngetCh1, fUngetCh2;
	private boolean					fLinenoValid;
	
	public SVArgFilePreProcOutput(
			StringBuilder 		text,
			List<Integer>		line_map) {
		fText = text;
		fIdx = 0;
		fLineIdx = 0;
		fLineMap = line_map;
		
		if (line_map.size() > 0) {
			fNextLinePos = line_map.get(0);
		} else {
			fNextLinePos = Integer.MAX_VALUE;
		}
		fLineno = 1;
	
		int length = fText.length();
		for (int i=0; i<length; i++) {
			if (fText.charAt(i) == '\r') {
				fText.setCharAt(i, '\n');
			}
		}
		fUngetCh1 = -1;
		fUngetCh2 = -1;
	}
	
	public List<Integer> getLineMap() {
		return fLineMap;
	}

	public int get_ch() {
		int ch = -1;
		if (fUngetCh1 != -1) {
			ch = fUngetCh1;
			fUngetCh1 = fUngetCh2;
			fUngetCh2 = -1;
		} else if (fIdx < fText.length()) {
			ch = fText.charAt(fIdx++);
			fLinenoValid = false;
		}
		
		if (ch > 127) {
			ch = AbstractTextScanner.unicode2ascii(ch);
		}
		
		return ch;
	}

	public void unget_ch(int ch) {
		fUngetCh2 = fUngetCh1;
		fUngetCh1 = ch;
	}

	public ScanLocation getLocation() {
		// Spin the line location forward if necessary
		if (fIdx >= fNextLinePos) {
			// Need to move forward
			while (fLineIdx < fLineMap.size() &&
					fLineMap.get(fLineIdx) < fIdx) {
				fLineIdx++;
				fLineno++;
			}
		
			// Once we reach the last line, ensure we
			// don't keep doing this
			if (fLineIdx >= fLineMap.size()) {
				fNextLinePos = Integer.MAX_VALUE;
			}
		}
		
		return new ScanLocation("", fLineno, 1);
	}
	
	@Override
	public int getLineno() {
		if (!fLinenoValid) {
			update_location();
		}
		return fLineno;
	}

	@Override
	public int getLinepos() {
		if (!fLinenoValid) {
			update_location();
		}
		return fLinepos;
	}

	@Override
	public int getFileId() {
	//	if (!fLinenoValid) {
	//		update_location();
	//	}
		return 0;
	}

	public void update_location() {
		// Spin the line location forward if necessary
		if (fIdx >= fNextLinePos) {
			// Need to move forward
			while (fLineIdx < fLineMap.size() &&
					fLineMap.get(fLineIdx) < fIdx) {
				fLineIdx++;
				fLineno++;
			}
		
			// Once we reach the last line, ensure we
			// don't keep doing this
			if (fLineIdx >= fLineMap.size()) {
				fNextLinePos = Integer.MAX_VALUE;
			}
		}
		
		fLinenoValid = true;
	}

	public long getPos() {
		return fIdx;
	}

	public String toString() {
		return fText.toString();
	}
}
