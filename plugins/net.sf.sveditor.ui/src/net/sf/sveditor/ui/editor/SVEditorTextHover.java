package net.sf.sveditor.ui.editor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;

public class SVEditorTextHover implements ITextHover /*, ITextHoverExtension */ {
	
	public SVEditorTextHover(SVEditor editor, ITextViewer viewer) {
		
	}

	public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
		System.out.println("getHoverInfo: " + hoverRegion.getOffset() + ", " + hoverRegion.getLength());
		String str = null;
		try {
			str = textViewer.getDocument().get(
					hoverRegion.getOffset(), hoverRegion.getLength());
			System.out.println("    " + str);
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		// TODO Auto-generated method stub
		return str;
	}

	public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
		System.out.println("getHoverRegion: " + offset);
		return findWord(textViewer.getDocument(), offset);
	}
	
	public IInformationControlCreator getHoverControlCreator() {
		// TODO Auto-generated method stub
		return null;
	}

	private IRegion findWord(IDocument document, int offset) {
		int start= -2;
		int end= -1;

		try {

			int pos= offset;
			char c;

			while (pos >= 0) {
				c= document.getChar(pos);
				if (!Character.isUnicodeIdentifierPart(c))
					break;
				--pos;
			}

			start= pos;

			pos= offset;
			int length= document.getLength();

			while (pos < length) {
				c= document.getChar(pos);
				if (!Character.isUnicodeIdentifierPart(c))
					break;
				++pos;
			}

			end= pos;

		} catch (BadLocationException x) {
		}

		if (start >= -1 && end > -1) {
			if (start == offset && end == offset)
				return new Region(offset, 0);
			else if (start == offset)
				return new Region(start, end - start);
			else
				return new Region(start + 1, end - start - 1);
		}

		return null;
	}

}
