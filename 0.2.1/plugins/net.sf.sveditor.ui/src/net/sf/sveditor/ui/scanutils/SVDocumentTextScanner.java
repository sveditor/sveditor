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


package net.sf.sveditor.ui.scanutils;

import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

public class SVDocumentTextScanner 
	extends AbstractTextScanner implements IBIDITextScanner {
	
	private IDocument				fDoc;
	private int						fIdx;
	private int						fOffset;
	private int						fLimit;
	private String					fName;
	private int						fUngetCh;
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			String					name,
			int						offset,
			boolean 				scan_fwd) {
		fDoc     = doc;
		fName    = name;
		fOffset  = -1;
		fIdx  	 = offset;
		fScanFwd = scan_fwd;
		fUngetCh = -1;
		fLimit   = -1;
	}
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset) {
		this(doc, "", offset, true);
	}

	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset,
			int						limit) {
		this(doc, "", offset, true);
		fOffset = offset;
		fLimit  = limit;
	}

	public void setScanFwd(boolean scan_fwd) {
		// TODO: I'm not sure switching directions is quite so simple
		if (fScanFwd != scan_fwd) {
			fUngetCh = -1;
		}
		super.setScanFwd(scan_fwd);
	}
	
	public long getPos() {
		return (long)fIdx;
	}
	
	public void seek(long pos) {
		fIdx = (int)pos;
		fUngetCh = -1;
	}
	
	public String get_str(long start, int length) {
		try {
			return fDoc.get((int)start, length);
		} catch (BadLocationException e) {
			e.printStackTrace();
			return null;
		}
	}

	public ScanLocation getLocation() {
		int lineno = -1;
		
		try {
			int off = fIdx < (fDoc.getLength())?fIdx:fDoc.getLength()-1;
			lineno = fDoc.getLineOfOffset(off);
		} catch (BadLocationException e) {}
		
		return new ScanLocation(fName, lineno, 0);
	}

	public int get_ch() {
		int ch = -1;
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
		} else {
			try {
				if (fScanFwd) {
					if ((fLimit == -1 && (fIdx < fDoc.getLength())) ||
						(fLimit != -1 && (fIdx <= fLimit))) {
						ch = fDoc.getChar(fIdx);
						fIdx++;
					}
				} else {
					if (fIdx >= fOffset) {
						ch = fDoc.getChar(fIdx);
						fIdx--;
					}
				}
			} catch (BadLocationException e) { }
		}
		
		return ch;
	}

	public void unget_ch(int ch) {
		if (fScanFwd) {
			fIdx--;
		} else {
			fIdx++;
		}
	}

}
