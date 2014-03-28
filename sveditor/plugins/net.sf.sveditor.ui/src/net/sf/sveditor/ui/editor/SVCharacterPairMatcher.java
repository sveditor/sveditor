/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ICharacterPairMatcher;

public class SVCharacterPairMatcher implements ICharacterPairMatcher {
	
	private final static char fPairs[] = {
		'{', '}',
		'<', '>',
		'[', ']',
		'(', ')'
	};
	
	private int							fStartPos;
	private int							fEndPos;
	private int							fAnchor;

	public void clear() {}

	public void dispose() {
		clear();
	}

	public int getAnchor() {
		return fAnchor;
	}

	public IRegion match(IDocument document, int offset) {
		IBIDITextScanner scanner = new SVDocumentTextScanner(document, "", offset, true, true);
		
		if ((document == null) || (offset < 0)) {
			
		}
		
		if (offset < 0) {
			return null;
		}
		
		if (document != null && matchPairsAt(scanner) && fStartPos != fEndPos) {
			return new Region(fStartPos, fEndPos - fStartPos + 1);
		}
		
		return null;
	}
	
	private boolean matchPairsAt(IBIDITextScanner scanner) {
		int i;
		int pairIndex1 = fPairs.length;
		int pairIndex2 = fPairs.length;
	
		long pos = scanner.getPos();
		int curr_char = scanner.get_ch();
		scanner.seek(pos);
		scanner.setScanFwd(false);

		fStartPos = -1;
		fEndPos = -1;
		// get the char preceding the start position
		scanner.get_ch();
		int prev_char = scanner.get_ch(); // fDocument.getgetChar(Math.max(fOffset - 1, 0));
		
		// search for opening peer character next to the activation point
		for (i = 0; i < fPairs.length; i = i + 2) {
			if (prev_char == fPairs[i]) {
				fStartPos = (int)(pos-1);
				pairIndex1 = i;
			} else if (curr_char == fPairs[i]) {
				fStartPos = (int)pos;
				pairIndex1 = i;
			}
		}
		
		// search for closing peer character next to the activation point
		for (i = 1; i < fPairs.length; i = i + 2) {
			if (curr_char == fPairs[i]) {
				fEndPos = (int)(pos);
				pairIndex2 = i;
			} else if (prev_char == fPairs[i]) {
				fEndPos = (int)(pos-1);
				pairIndex2 = i;
			}
		}

		if (fEndPos > -1) {
			fAnchor = RIGHT;
			scanner.setScanFwd(false);
			scanner.seek(fEndPos);
			fStartPos = searchForOpeningPeer(scanner, fPairs[pairIndex2 - 1],
					fPairs[pairIndex2]);
			if (fStartPos > -1) {
				return true;
			} else {
				fEndPos = -1;
			}
		} else if (fStartPos > -1) {
			fAnchor = LEFT;
			scanner.setScanFwd(true);
			scanner.seek(fStartPos);
			fEndPos = searchForClosingPeer(scanner, fPairs[pairIndex1],
					fPairs[pairIndex1 + 1]);
			if (fEndPos > -1) {
				return true;
			} else {
				fStartPos = -1;
			}
		}

		return false;
	}

	/**
	 * Basic search for ClosingPeer
	 */
	private int searchForClosingPeer(IBIDITextScanner scanner, char opening, char closing) {
		int depth = 0;

		int ch = 0;
		while (true) {
			while ((ch = scanner.get_ch()) != -1) {
				if (ch =='"') {
					int last_ch = ch;
					while ((ch = scanner.get_ch()) != -1) {
						if (ch == '"' && last_ch != '\\') {
							break;
						}
						last_ch = ch;
					}
				}

				if (ch == opening || ch == closing) {
					break;
				}
			}
			if (ch == -1) {
				return -1;
			}
			if (ch == opening) {
				depth++;
			} else {
				depth--;
			}
			if (depth == 0) {
				if (scanner.getPos() > 0) {
					return (int)(scanner.getPos()-1);
				} else {
					return (int)scanner.getPos();
				}
			}
		}
	}

	/**
	 * Basic search for OpeningPeer
	 */
	private int searchForOpeningPeer(IBIDITextScanner scanner, char opening, char closing) {
		int depth = 0;
		int ch = 0;
		while (true) {
			while ((ch = scanner.get_ch()) != -1) {
				if (ch =='"') {
					while ((ch = scanner.get_ch()) != -1) {
						if (ch == '"') { 
							int prev_ch = scanner.get_ch();
							if (prev_ch != '\\') {
								// not escaped quote, done
								scanner.unget_ch(prev_ch);
								break;
							}
						}
					}
				}
				if (ch == opening || ch == closing) {
					break;
				}
			}
			if (ch == -1) {
				return -1;
			}
			if (ch == closing) {
				depth++;
			} else {
				depth--;
			}
			if (depth == 0) {
				return (int)(scanner.getPos()+1);
			}
		}
	}
}
