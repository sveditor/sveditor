package net.sf.sveditor.ui.scanutils;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVDocumentTextScanner 
	extends AbstractTextScanner implements IBIDITextScanner {
	
	private IDocument				fDoc;
	private int						fOffset;
	private String					fName;
	private int						fUngetCh;
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			String					name,
			int						offset,
			boolean 				scan_fwd) {
		fDoc     = doc;
		fName    = name;
		fOffset  = offset;
		fScanFwd = scan_fwd;
		fUngetCh = -1;
	}
	
	public SVDocumentTextScanner(
			IDocument 				doc,
			int						offset) {
		this(doc, "", offset, true);
	}
	
	public void setScanFwd(boolean scan_fwd) {
		// TODO: I'm not sure switching directions is quite so simple
		if (fScanFwd != scan_fwd) {
			fUngetCh = -1;
		}
		super.setScanFwd(scan_fwd);
	}
	
	public long getPos() {
		return (long)fOffset;
	}
	
	public void seek(long pos) {
		fOffset = (int)pos;
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
			int off = fOffset < (fDoc.getLength())?fOffset:fDoc.getLength()-1;
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
					if (fOffset < fDoc.getLength()) {
						ch = fDoc.getChar(fOffset);
						fOffset++;
					}
				} else {
					if (fOffset >= 0) {
						ch = fDoc.getChar(fOffset);
						fOffset--;
					}
				}
			} catch (BadLocationException e) { }
		}
		
		return ch;
	}

	public void unget_ch(int ch) {
		if (fScanFwd) {
			fOffset--;
		} else {
			fOffset++;
		}
	}

}
