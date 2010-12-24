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


public class StringTextScanner extends AbstractTextScanner 
	implements IRandomAccessTextScanner {
	private StringBuilder		fStr;
	private int					fIdx;
	private int					fLimit;
	private int					fUngetCh;
	
	public StringTextScanner(StringTextScanner scanner, int idx) {
		fStr   = scanner.getStorage();
		fIdx   = idx;
		fLimit = -1;
		fUngetCh = -1;
	}

	public StringTextScanner(StringTextScanner scanner) {
		fStr   = scanner.getStorage();
		fIdx   = scanner.getOffset();
		fLimit = -1;
		fUngetCh = -1;
	}

	public StringTextScanner(StringTextScanner scanner, int idx, int limit) {
		fStr   = scanner.getStorage();
		fIdx   = idx;
		fLimit = limit;
		fUngetCh = -1;
	}

	public StringTextScanner(StringBuilder str) {
		init(str);
		fUngetCh = -1;
	}
	
	public StringTextScanner(String str) {
		this(new StringBuilder(str));
	}

	public StringTextScanner(String str, int idx) {
		this(new StringBuilder(str), idx);
	}

	public StringTextScanner(StringBuilder str, int idx) {
		init(str, idx);
	}

	public void init(StringBuilder str) {
		init(str, 0);
	}
	
	public void init(StringBuilder str, int idx) {
		fStr   = str;
		fIdx   = idx;
		fLimit = -1;
		
		fUngetCh = -1;
	}
	
	public String get_str(long start, int length) {
		if (length == 0) {
			return "";
		} else {
			return fStr.substring((int)start, (int)(start+length-1));
		}
	}

	public long getPos() {
		return fIdx;
	}

	public void seek(long pos) {
		fIdx = (int)pos;
	}

	public int get_ch() {
		int ch = -1;
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
			return ch;
		} else if (fIdx < fStr.length() && 
				(fLimit == -1 || fIdx < fLimit)) {
			ch = fStr.charAt(fIdx);
			fIdx++;
		}
		
		if (ch != -1 && fCaptureEnabled) {
			fCaptureBuffer.append((char)ch);
		}
		
		if (fLastCh == '\n') {
			fLineno++;
		}
		fLastCh = ch;
		
		return ch;
	}
	
	public void unget_ch(int ch) {
		fUngetCh = ch;
	}
	
	public int getOffset() {
		return fIdx;
	}
	
	public void seek(int idx) {
		fIdx = idx;
	}
	
	public StringBuilder getStorage() {
		return fStr;
	}
	
	public int getLimit() {
		return (fLimit != -1)?fLimit:fStr.length();
	}
	
	private void update_idx_replace(int start, int end, int len) {
		if (start < fIdx) {
			fIdx += (len-(end-start));
		}
		if (fLimit != -1) {
			fLimit += (len - (end-start));
		}
		
		/*
		if (fParent != null) {
			fParent.update_idx_replace(start, end, len);
		}
		 */
	}
	
	public void replace(int start, int end, String replace) {
		try {
			fStr.replace(start, end, replace);
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println("replace " + start + ", " + end + ", \"" + replace + "\"");
		}
		
		update_idx_replace(start, end, replace.length());
	}
	
	private void update_idx_delete(int start, int end) {
		if (start < fIdx) {
			if (end > fIdx) {
				fIdx -= (fIdx - start);
			} else {
				fIdx -= (end - start);
			}
		}

		if (fLimit != -1) {
			fLimit -= (end-start);
		}
	
		/*
		if (fParent != null) {
			fParent.update_idx_delete(start, end);
		}
		 */
	}
	
	public void delete(int start, int end) {
		fStr.delete(start, end);
		
		update_idx_delete(start, end);
	}
	
	public String substring(int start, int end) {
		if (end > fStr.length()) {
			System.out.println("end " + end + " outside legal range of " + fStr.length());
		}
		return fStr.substring(start, end);
	}
	
	public String substring(int start) {
		return fStr.substring(start);
	}
	
	public ScanLocation getLocation() {
		return new ScanLocation("UNKNOWN", fLineno, 0);
	}
}
