package net.sf.sveditor.core.preproc;

import java.util.List;

import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcOutput extends AbstractTextScanner {
	private StringBuilder				fText;
	private List<Integer>				fLineMap;
	private int						fLineIdx;
	private int						fNextLinePos;
	private int						fIdx;
	
	public SVPreProcOutput(
			StringBuilder 		text,
			List<Integer>		line_map) {
		fText = text;
		fIdx = 0;
		fLineIdx = 0;
		fLineMap = line_map;
		if (line_map.size() > 1) {
			fNextLinePos = line_map.get(1);
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
	}

	public int get_ch() {
		if (fIdx < fText.length()) {
			return fText.charAt(fIdx++);
		} else {
			return -1;
		}
	}

	public void unget_ch(int ch) {
		if (fIdx > 0 && ch != -1) {
			fIdx--;
		}
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

	public long getPos() {
		return fIdx;
	}

	public String toString() {
		return fText.toString();
	}
}
