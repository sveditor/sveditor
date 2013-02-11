package net.sf.sveditor.core.preproc;

import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcOutput extends AbstractTextScanner {
	private StringBuilder					fText;
	private SVDBFileTree					fFileTree;
	private List<Integer>					fLineMap;
	private int								fLineIdx;
	private int								fNextLinePos;
	private List<Tuple<Integer,Integer>>	fFileMap;
	private List<String>					fFileList;
	private List<Integer>					fFileIdList;
	private int								fFileId;
	private int								fFileIdx;
	private int								fNextFilePos;
	private int								fIdx;
	private int								fUngetCh1, fUngetCh2;
	
	public SVPreProcOutput(
			StringBuilder 					text,
			List<Integer>					line_map,
			List<Tuple<Integer,Integer>>	file_map,
			List<String>					file_list) {
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
		
		fFileIdx = 0;
		fFileMap = file_map;
		fFileList = file_list;
		/*
		if (file_map.size() > 0) {
			fNextFilePos = line_map.get(1);
		} else {
			fNextFilePos = Integer.MAX_VALUE;
		}
		 */
		fNextFilePos = -1;
	
		int length = fText.length();
		for (int i=0; i<length; i++) {
			if (fText.charAt(i) == '\r') {
				fText.setCharAt(i, '\n');
			}
		}
		fUngetCh1 = -1;
		fUngetCh2 = -1;
	}
	
	public void setFileTree(SVDBFileTree ft) {
		fFileTree = ft;
	}
	
	public SVDBFileTree getFileTree() {
		return fFileTree;
	}
	
	public List<String> getFileList() {
		return fFileList;
	}
	
	public void setFileIdList(List<Integer> id_list) {
		fFileIdList = id_list;
	}
	
	public int get_ch() {
		int ch = -1;
		if (fUngetCh1 != -1) {
			ch = fUngetCh1;
			fUngetCh1 = fUngetCh2;
			fUngetCh2 = -1;
		} else if (fIdx < fText.length()) {
			ch = fText.charAt(fIdx++);
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
		
		if (fIdx >= fNextFilePos) {
			// Move forward to next file ID
			while (fFileIdx < fFileMap.size() &&
					fFileMap.get(fFileIdx).first() < fIdx) {
				fFileIdx++;
			}
			
			if (fFileIdx >= fFileMap.size()) {
				fNextFilePos = Integer.MAX_VALUE;
			} else {
				fFileId = fFileMap.get(fFileIdx).second();
			}
		
			// If we have independent file id's, get it now
			if (fFileIdList != null) {
				fFileId = fFileIdList.get(fFileId);
			}
		}
		
		return new ScanLocation(fFileId, fLineno, 1);
	}

	public long getPos() {
		return fIdx;
	}

	public String toString() {
		return fText.toString();
	}
}
