/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui.scanutils;

import org.eclipse.hdt.sveditor.core.scanutils.AbstractTextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.IBIDITextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.ScanLocation;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.ITypedRegion;

public class SVDocumentTextScannerBase 
	extends AbstractTextScanner implements IBIDITextScanner {
	
	protected IDocument				fDoc;
	protected int						fIdx;
	protected int						fOffset;
	protected int						fLimit;
	protected String					fName;
	protected int						fUngetCh;
	protected boolean					fSkipComments;
	protected String					fDocPartition;
	protected String					fDocCommentPartitions[];

	public SVDocumentTextScannerBase(
			IDocument 				doc,
			String					doc_partition,
			String					doc_comment_partitions[],
			String					name,
			int						offset,
			boolean 				scan_fwd,
			boolean					skip_comments) {
		fDocPartition = doc_partition;
		fDocCommentPartitions = doc_comment_partitions;
		fDoc     = doc;
		fName    = name;
		fOffset  = -1;
		fIdx  	 = offset;
		fScanFwd = scan_fwd;
		fUngetCh = -1;
		fLimit   = -1;
		fSkipComments = skip_comments;
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
		return (long)((fIdx>0)?fIdx:0);
	}
	
	public long getRealPos() {
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
		int linepos = -1;
		
		try {
			int off = fIdx < (fDoc.getLength())?fIdx:fDoc.getLength()-1;
			lineno = fDoc.getLineOfOffset(off);
			linepos = off-fDoc.getLineOffset(off);
		} catch (BadLocationException e) {}
		
		return new ScanLocation(fName, lineno, linepos);
	}
	
	protected boolean isCommentPartition(ITypedRegion r) {
		for (String cp : fDocCommentPartitions) {
			if (r.getType().equals(cp)) {
				return true;
			}
		}
		return false;
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
							r = ext3.getPartition(fDocPartition, fIdx, false);
						} catch (BadPartitioningException e) {}
								
						if (!fSkipComments || (r != null && !isCommentPartition(r))) {
							ch = fDoc.getChar(fIdx);
							fIdx++;
							break;
						} else {
							// Start of comment ... return immediately
							if (fIdx == r.getOffset()) {
								ch = ' ';
								fIdx ++;
								break;
							}
							// End of comment ... return
							else if (fIdx == (r.getOffset() + r.getLength()-1)) {
								ch = ' ';
								fIdx++;
								break;
							}
							// Enter in the middle of a comment ... jump to end and return
							else if ((fIdx > r.getOffset()) && (fIdx < (r.getOffset()+r.getLength()-1))) {
								// Interpret a comment as a single whitespace char to
								// prevent cross-comment content assist
								fIdx = r.getOffset()+r.getLength();
								ch = ' ';
								break;
							} else {
								fIdx++;
							}
						}
					}
				}
				// Scanning backwards
				else {
					while (fIdx >= fOffset) {
						ITypedRegion r = null;
						try {
							r = ext3.getPartition(fDocPartition, fIdx, false);
						} catch (BadPartitioningException e) {
							System.out.println("badLocation: " + fIdx);
							break;
						}
						
						if (!fSkipComments || (r != null && !isCommentPartition(r))) {
							if (fIdx >= fDoc.getLength()) {
								fIdx = fDoc.getLength()-1;
							}
							ch = fDoc.getChar(fIdx);
							fIdx--;
							break;
						} else {
							// Start of comment ... return immediately
							if (fIdx == r.getOffset()) {
								ch = ' ';
								fIdx--;
								break;
							}
							// End of comment ... return immediately
							else if (fIdx == (r.getOffset() + r.getLength()-1)) {
								ch = ' ';
								fIdx --;
								break;
							}
							// Enter in the middle of a comment ... jump to start and return
							else if ((fIdx > r.getOffset()) && (fIdx < (r.getOffset()+r.getLength()-1))) {
								fIdx = r.getOffset();
								ch = ' ';
								break;
							} else {
								fIdx--;
							}
						}
					}
				}
			} catch (BadLocationException e) {}
		}
		
		if (ch > 127) {
			ch = AbstractTextScanner.unicode2ascii(ch);
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
