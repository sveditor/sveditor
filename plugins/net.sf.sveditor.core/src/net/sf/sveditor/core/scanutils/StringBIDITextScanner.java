package net.sf.sveditor.core.scanutils;

import java.util.ArrayList;
import java.util.List;

public class StringBIDITextScanner 
	extends AbstractTextScanner implements IBIDITextScanner {
	private String				fData;
	private int					fIdx;
	private boolean				fScanFwd;
	private int					fUngetCh;
	List<Integer>				fLineOffsets;
	
	public StringBIDITextScanner(String data) {
		fData    = data;
		fIdx     = 0;
		fScanFwd = true;
		fUngetCh = -1;
		
		fLineOffsets = new ArrayList<Integer>();
		fLineOffsets.add(0);
		
		for (int i=0; i<fData.length(); i++) {
			if (fData.charAt(i) == '\n') {
				fLineOffsets.add(i+1);
			}
		}
	}

	public boolean getScanFwd() {
		return fScanFwd;
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
				if ((fIdx-1) >= 0) {
					fIdx--;
					ret = fData.charAt(fIdx);
				}
			}
		}

		return ret;
	}

	public ScanLocation getLocation() {
		int lineno = -1;
		
		for (int i=0; i<fLineOffsets.size(); i++) {
			int pos = fLineOffsets.get(i);
			if (fIdx <= pos) {
				lineno = i;
				break;
			}
		}
		
		return new ScanLocation("", lineno, 0);
	}

	public void unget_ch(int ch) {
		fUngetCh = ch;
	}

	public String get_str(long start, int length) {
		System.out.println("get_str() " + start + ":" + length + " str length=" + fData.length());
		return fData.substring((int)start, (int)start+length);
	}

	public long getPos() {
		return fIdx;
	}

	public void seek(long pos) {
		fIdx = (int)pos;
	}

	
}
