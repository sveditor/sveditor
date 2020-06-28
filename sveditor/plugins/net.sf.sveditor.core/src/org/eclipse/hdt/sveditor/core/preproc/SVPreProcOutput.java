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
package org.eclipse.hdt.sveditor.core.preproc;

import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.scanutils.AbstractTextScanner;

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
	
	private StringBuilder						fText;
	private int									fTextLength;
	private SVDBFileTree						fFileTree;

	private int									fFileId;
	private int									fIdx;
	private int									fLastCh;
	private boolean								fIncLineno;
	private int									fUngetCh1, fUngetCh2;
	private ISVPreProcOutputFileChangeListener	fFileChangeListener;
	
	public SVPreProcOutput(StringBuilder text) {
		fText = text;
		fIdx = 0;
		
		fLineno = 1;
		fIncLineno = true;
		fFileId = -1;
		
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
	
	public void setFileChangeListener(ISVPreProcOutputFileChangeListener l) {
		fFileChangeListener = l;
	}
	
	public SVPreProcOutput duplicate() {
		return new SVPreProcOutput(fText);
	}
	
	public void setFileTree(SVDBFileTree ft) {
		fFileTree = ft;
	}
	
	public SVDBFileTree getFileTree() {
		return fFileTree;
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
		
			// Only expect `line directives
			if (ch == '`' && fIdx < fText.length() && fText.charAt(fIdx) == 'l') {
				int start = fIdx;
				// Directive
				String line;
				
				while (fIdx < fText.length() && fText.charAt(fIdx++) != '\n') { }
				line = fText.substring(start, fIdx-1);
				
				int ws_idx = line.indexOf(' ');
				int colon_idx = line.indexOf(':', ws_idx);
				int colon2_idx = line.indexOf(':', colon_idx+1);
				
				try {
					if (ws_idx != -1 && colon_idx != -1) {
						int new_file = Integer.parseInt(line.substring(ws_idx+1, colon_idx));
						
						if (fFileId != new_file && fFileChangeListener != null) {
							fFileChangeListener.fileChanged(fFileId, new_file);
						}
						
						fFileId = new_file;
					}
				} catch (NumberFormatException e) {
					e.printStackTrace();
				}
				
				try {
					if (colon_idx != -1 && colon2_idx != -1) {
						fLineno = Integer.parseInt(line.substring(colon_idx+1, colon2_idx));
					}
				} catch (NumberFormatException e) {
					e.printStackTrace();
				}
				
				try {
					if (colon2_idx != -1) {
						int inc = Integer.parseInt(line.substring(colon2_idx+1));
						fIncLineno = (inc==1);
					}
				} catch (NumberFormatException e) {
					e.printStackTrace();
				}
				
				ch = (fIdx < fText.length())?fText.charAt(fIdx++):-1;
			} else if (fLastCh == '\n' && fIncLineno) {
				fLineno++;
			}
			fLastCh = ch;
		}
		return ch;
	}

	public void unget_ch(int ch) {
		fUngetCh2 = fUngetCh1;
		fUngetCh1 = ch;
	}
	
	
	@Override
	public int getFileId() {
		return fFileId;
	}
	
	public void setFileId(int file_id) {
		fFileId = file_id;
	}

	@Override
	public int getLineno() {
		return fLineno;
	}

	@Override
	public int getLinepos() {
		return fLinepos;
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
