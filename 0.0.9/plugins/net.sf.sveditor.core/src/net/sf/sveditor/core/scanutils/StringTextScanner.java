package net.sf.sveditor.core.scanutils;


public class StringTextScanner extends AbstractTextScanner {
	private StringBuilder	fStr;
	private int				fIdx;
	private int				fLimit;
	private int				fUngetCh;
	
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
	
	public void replace(int start, int end, String replace) {
		try {
			fStr.replace(start, end, replace);
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println("replace " + start + ", " + end + ", \"" + replace + "\"");
		}
		
		if (start < fIdx) {
			fIdx += (replace.length()-(end-start));
		}
		
		if (fLimit != -1) {
			fLimit += (replace.length() - (end-start));
		}
	}
	
	public void delete(int start, int end) {
		fStr.delete(start, end);
		
		if (start <= fIdx) {
			if (end > fIdx) {
				fIdx -= (fIdx - start);
			} else {
				fIdx -= (end - start);
			}
		}

		if (fLimit != -1) {
			fLimit -= (end-start);
		}
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
