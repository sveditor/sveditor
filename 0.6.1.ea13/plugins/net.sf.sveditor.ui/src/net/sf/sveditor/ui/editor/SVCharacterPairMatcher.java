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

import org.eclipse.jface.text.BadLocationException;
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
	
	private IDocument					fDocument;
	private int							fOffset;
	private int							fStartPos;
	private int							fEndPos;
	private int							fAnchor;

	public void clear() {}

	public void dispose() {
		clear();
		fDocument = null;
	}

	public int getAnchor() {
		return fAnchor;
	}

	public IRegion match(IDocument document, int offset) {
		fOffset = offset;
		
		if (fOffset < 0) {
			return null;
		}
		
		fDocument = document;
		
		if (fDocument != null && matchPairsAt() && fStartPos != fEndPos) {
			return new Region(fStartPos, fEndPos - fStartPos + 1);
		}
		
		return null;
	}
	
	private boolean matchPairsAt() {
		int i;
		int pairIndex1 = fPairs.length;
		int pairIndex2 = fPairs.length;

		fStartPos = -1;
		fEndPos = -1;
		// get the char preceding the start position
		try {
			char prevChar = fDocument.getChar(Math.max(fOffset - 1, 0));
			// search for opening peer character next to the activation point
			for (i = 0; i < fPairs.length; i = i + 2) {
				if (prevChar == fPairs[i]) {
					fStartPos = fOffset - 1;
					pairIndex1 = i;
				}
			}
			// search for closing peer character next to the activation point
			for (i = 1; i < fPairs.length; i = i + 2) {
				if (prevChar == fPairs[i]) {
					fEndPos = fOffset - 1;
					pairIndex2 = i;
				}
			}
			if (fEndPos > -1) {
				fAnchor = RIGHT;
				fStartPos = searchForOpeningPeer(fEndPos, fPairs[pairIndex2 - 1],
						fPairs[pairIndex2]);
				if (fStartPos > -1)
					return true;
				else
					fEndPos = -1;
			} else if (fStartPos > -1) {
				fAnchor = LEFT;
				fEndPos = searchForClosingPeer(fStartPos, fPairs[pairIndex1],
						fPairs[pairIndex1 + 1]);
				if (fEndPos > -1)
					return true;
				else
					fStartPos = -1;
			}

		} catch (BadLocationException x) {
		}
		return false;
	}

	/**
	 * Basic search for ClosingPeer
	 */
	private int searchForClosingPeer(int start, char opening, char closing) {
		try {
			int depth = 1;
			int fPos = start+1;
			char fChar = 0;
			while (true) {
				while (fPos < fDocument.getLength()) {
					fChar = fDocument.getChar(fPos);
					if (fChar =='"')
						while (fDocument.getChar(++fPos) !='"')
							;
					if (fChar == opening || fChar == closing)
						break;
					fPos++;
				}
				if (fPos == fDocument.getLength())
					return -1;
				if (fChar == opening)
					depth++;
				else
					depth--;        
				if (depth == 0)
					return fPos;
				fPos++;        
			}
		} catch (BadLocationException e) {
			return -1;
		}
	}

	/**
	 * Basic search for OpeningPeer
	 */
	private int searchForOpeningPeer(int start, char opening, char closing) {
		try {
			int depth = 1;
			int fPos = start-1;
			char fChar = 0;
			while (true) {
				while (fPos > -1) {
					fChar = fDocument.getChar(fPos);
					if (fChar =='"')
						while (fDocument.getChar(--fPos) !='"')
							;
					if (fChar == opening || fChar == closing)
						break;
					fPos--;
				}
				if (fPos == -1)
					return -1;
				if (fChar == closing)
					depth++;
				else
					depth--;
				if (depth == 0)
					return fPos;
				fPos--;
			}

		} catch (BadLocationException e) {
			return -1;
		}
	}
}
