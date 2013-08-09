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
		
		scanner.setScanFwd(false);

		fStartPos = -1;
		fEndPos = -1;
		// get the char preceding the start position
		int prevChar = scanner.get_ch(); // fDocument.getgetChar(Math.max(fOffset - 1, 0));

		// search for opening peer character next to the activation point
		for (i = 0; i < fPairs.length; i = i + 2) {
			if (prevChar == fPairs[i]) {
				fStartPos = (int)(scanner.getPos()+1); // fOffset - 1;
				pairIndex1 = i;
			}
		}
		// search for closing peer character next to the activation point
		for (i = 1; i < fPairs.length; i = i + 2) {
			if (prevChar == fPairs[i]) {
				fEndPos = (int)(scanner.getPos()+1); // fOffset - 1;
				pairIndex2 = i;
			}
		}

		if (fEndPos > -1) {
			fAnchor = RIGHT;
			fStartPos = searchForOpeningPeer(scanner, fEndPos, fPairs[pairIndex2 - 1],
					fPairs[pairIndex2]);
			if (fStartPos > -1) {
				return true;
			} else {
				fEndPos = -1;
			}
		} else if (fStartPos > -1) {
			fAnchor = LEFT;
			fEndPos = searchForClosingPeer(scanner, fStartPos, fPairs[pairIndex1],
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
	private int searchForClosingPeer(IBIDITextScanner scanner, int start, char opening, char closing) {
		scanner.setScanFwd(true);
		scanner.seek(fStartPos+1);

		int depth = 1;

		int ch = 0;
		while (true) {
			while ((ch = scanner.get_ch()) != -1) {
				if (ch =='"') {
					while ((ch = scanner.get_ch()) !='"') { }
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
	private int searchForOpeningPeer(IBIDITextScanner scanner, int start, char opening, char closing) {
		scanner.setScanFwd(false);
		int depth = 1;
		int ch = 0;
		while (true) {
			while ((ch = scanner.get_ch()) != -1) {
				if (ch =='"') {
					while ((ch = scanner.get_ch()) != '"') { }
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
