package net.sf.sveditor.core.preproc;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;

public class SVPreProcOutput extends AbstractTextScanner {
	
	public static class FileChangeInfo {
		public int				fStartIdx;
		public int				fFileId;
		public int				fLineno;
		
		public FileChangeInfo(int start, int id, int lineno) {
			fStartIdx = start;
			fFileId = id;
			fLineno = lineno;
		}
	}
	
	private StringBuilder					fText;
	private int								fTextLength;
	private SVDBFileTree					fFileTree;
	private List<Integer>					fLineMap;
	private int								fLineIdx;
	private int								fNextLinePos;
	private List<FileChangeInfo>			fFileMap;
	private List<String>					fFileList;
	private int								fFileId;
	private int								fFileIdx;
	private int								fNextFilePos;
	private int								fIdx;
	private int								fUngetCh1, fUngetCh2;
	private boolean							fLineValid;
	
	public SVPreProcOutput(
			StringBuilder 			text,
			List<Integer>			line_map,
			List<FileChangeInfo>	file_map,
			List<String>			file_list) {
		fText = text;
		fIdx = 0;
		
		fLineIdx = 0;
		fLineMap = line_map;
		if (line_map != null && line_map.size() > 1) {
			fNextLinePos = line_map.get(1);
		} else {
			fNextLinePos = Integer.MAX_VALUE;
			fLineMap = new ArrayList<Integer>();
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
		fTextLength = fText.length();
		fUngetCh1 = -1;
		fUngetCh2 = -1;
	}
	
	public SVPreProcOutput duplicate() {
		return new SVPreProcOutput(
				fText, 
				fLineMap,
				fFileMap,
				fFileList);
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
	
	public List<FileChangeInfo> getFileMap() {
		return fFileMap;
	}

	/*
	public void setFileIdList(List<Integer> id_list) {
		fFileIdList = id_list;
	}
	 */
	
	public int get_ch() {
		int ch = -1;
		if (fUngetCh1 != -1) {
			ch = fUngetCh1;
			fUngetCh1 = fUngetCh2;
			fUngetCh2 = -1;
		} else if (fIdx < fTextLength) {
			ch = fText.charAt(fIdx++);
			fLineValid = false;
		}
		return ch;
	}

	public void unget_ch(int ch) {
		fUngetCh2 = fUngetCh1;
		fUngetCh1 = ch;
	}
	
	
	@Override
	public int getFileId() {
		if (!fLineValid) {
			update_location();
		}
		return fFileId;
	}

	@Override
	public int getLineno() {
		if (!fLineValid) {
			update_location();
		}
		return fLineno;
	}

	@Override
	public int getLinepos() {
		if (!fLineValid) {
			update_location();
		}
		return fLinepos;
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
			} else {
				fNextLinePos = fLineMap.get(fLineIdx);
			}
		} 
		
		if (fIdx >= fNextFilePos && fFileMap.size() > 0) {
			// Move forward to find the next file ID
			while (fFileIdx < fFileMap.size() &&
					fFileMap.get(fFileIdx).fStartIdx < fIdx) {
				fFileIdx++;
			}
			
			if (fFileIdx >= fFileMap.size()) {
				fNextFilePos = Integer.MAX_VALUE;
				fFileId = fFileMap.get(fFileIdx-1).fFileId;
				fLineno = fFileMap.get(fFileIdx-1).fLineno;
			} else {
				fNextFilePos = fFileMap.get(fFileIdx).fStartIdx;
				if (fFileIdx > 0) {
					fFileId = fFileMap.get(fFileIdx-1).fFileId;
					fLineno = fFileMap.get(fFileIdx-1).fLineno;
				} else {
					fFileId = fFileMap.get(fFileIdx).fFileId;
					fLineno = fFileMap.get(fFileIdx).fLineno;
				}
			}
		}
		
		fLineValid = true;
	}

	public long getPos() {
		return fIdx;
	}

	public String toString() {
		return fText.toString();
	}
	
	public String dump() {
		StringBuilder ret = new StringBuilder();
		SVPreProcOutput out = duplicate();
		
		while (true) {
			int ch = out.get_ch();
			if (ch == -1) {
				break;
			}
			
//			ScanLocation tmp = out.getLocation();
//			if (loc == null || 
//					loc.getFileId() != tmp.getFileId() || 
//					loc.getLineNo() != tmp.getLineNo()) {
//				loc = tmp;
//				System.out.print("\n" + loc.getFileId() + ":" + loc.getLineNo() + " ");
//			}
			System.out.print((char)ch);
		}
	
		return ret.toString();
	}
}
