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
import net.sf.sveditor.ui.editor.SVDocumentPartitions;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.ITypedRegion;

public class SVDocumentTextScanner 
	extends AbstractTextScanner implements IBIDITextScanner {
	
	private IDocument				fDoc;
	private int						fIdx;
	private int						fOffset;
	private int						fLimit;
	private String					fName;
	private int						fUngetCh;
	private boolean					fSkipComments;
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			String					name,
			int						offset,
			boolean 				scan_fwd,
			boolean					skip_comments) {
		fDoc     = doc;
		fName    = name;
		fOffset  = -1;
		fIdx  	 = offset;
		fScanFwd = scan_fwd;
		fUngetCh = -1;
		fLimit   = -1;
		fSkipComments = skip_comments;
	}
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset) {
		this(doc, "", offset, true, false);
	}

	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset,
			int						limit) {
		this(doc, "", offset, true, false);
		fOffset = offset;
		fLimit  = limit;
	}
	
	public void setSkipComments(boolean skip_comments) {
		fSkipComments = skip_comments;
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
		
		// end.
		
		
		if (fUngetCh != -1) {
			ch = fUngetCh;
			fUngetCh = -1;
		} else {
			try {
				IDocumentExtension3 ext3 = (IDocumentExtension3)fDoc;
				if (fScanFwd) {
					while ((fLimit == -1 && (fIdx < fDoc.getLength())) ||
						(fLimit != -1 && (fIdx <= fLimit))) {
						ITypedRegion r = null;
						try {
							r = ext3.getPartition(SVDocumentPartitions.SV_PARTITIONING, fIdx, false);
						} catch (BadPartitioningException e) {}
								
						if (!fSkipComments ||
								(r != null && 
								!r.getType().equals(SVDocumentPartitions.SV_MULTILINE_COMMENT) &&
								!r.getType().equals(SVDocumentPartitions.SV_SINGLELINE_COMMENT))) {
							ch = fDoc.getChar(fIdx);
							fIdx++;
							break;
						} else {
							if (fIdx == r.getOffset()) {
								// Interpret a comment as a single whitespace char to
								// prevent cross-comment content assist
								ch = ' ';
								fIdx++;
								break;
							} else {
								fIdx++;
							}
						}
					}
				} else {
					while (fIdx >= fOffset) {
						ITypedRegion r = null;
						try {
							r = ext3.getPartition(SVDocumentPartitions.SV_PARTITIONING, fIdx, false);
						} catch (BadPartitioningException e) {}
								
						if (!fSkipComments ||
								(r != null && 
								!r.getType().equals(SVDocumentPartitions.SV_MULTILINE_COMMENT) &&
								!r.getType().equals(SVDocumentPartitions.SV_SINGLELINE_COMMENT))) {
							ch = fDoc.getChar(fIdx);
							fIdx--;
							break;
						} else {
							if (fIdx == (r.getOffset() + r.getLength()-1)) {
								ch = ' ';
								fIdx--;
								break;
							} else {
								fIdx--;
							}
						}
					}
				}
			} catch (BadLocationException e) {
			}
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
