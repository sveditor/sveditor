
/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package net.sf.sveditor.ui.doc;

import java.io.IOException;
import java.io.PushbackReader;
import java.io.Reader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Font;


/**
 * Reads the text contents from a reader of HTML contents and translates
 * the tags or cut them out.
 * <p>
 * Moved into this package from <code>org.eclipse.jface.internal.text.revisions</code>.</p>
 */
public class HTML2TextReader extends SubstitutionTextReader {

	private static final String EMPTY_STRING= ""; //$NON-NLS-1$
	private static final Map<String,String> fgEntityLookup;
	private static final Set<String> fgTags;
	private static final String BLOCK_SELECTION_MODE_FONT = "org.eclipse.ui.workbench.texteditor.blockSelectionModeFont";

	static {

		fgTags= new HashSet<String>();
		fgTags.add("b"); //$NON-NLS-1$
		fgTags.add("br"); //$NON-NLS-1$
		fgTags.add("br/"); //$NON-NLS-1$
		fgTags.add("div"); //$NON-NLS-1$
		fgTags.add("del"); //$NON-NLS-1$
		fgTags.add("i"); //$NON-NLS-1$
		fgTags.add("h1"); //$NON-NLS-1$
		fgTags.add("h2"); //$NON-NLS-1$
		fgTags.add("h3"); //$NON-NLS-1$
		fgTags.add("h4"); //$NON-NLS-1$
		fgTags.add("h5"); //$NON-NLS-1$
		fgTags.add("p"); //$NON-NLS-1$
		fgTags.add("dl"); //$NON-NLS-1$
		fgTags.add("dt"); //$NON-NLS-1$
		fgTags.add("dd"); //$NON-NLS-1$
		fgTags.add("li"); //$NON-NLS-1$
		fgTags.add("ul"); //$NON-NLS-1$
		fgTags.add("pre"); //$NON-NLS-1$
		fgTags.add("head"); //$NON-NLS-1$

		fgEntityLookup= new HashMap<String,String>(7);
		fgEntityLookup.put("lt", "<"); //$NON-NLS-1$ //$NON-NLS-2$
		fgEntityLookup.put("gt", ">"); //$NON-NLS-1$ //$NON-NLS-2$
		fgEntityLookup.put("nbsp", " "); //$NON-NLS-1$ //$NON-NLS-2$
		fgEntityLookup.put("amp", "&"); //$NON-NLS-1$ //$NON-NLS-2$
		fgEntityLookup.put("circ", "^"); //$NON-NLS-1$ //$NON-NLS-2$
		fgEntityLookup.put("tilde", "~"); //$NON-NLS-2$ //$NON-NLS-1$
		fgEntityLookup.put("quot", "\"");		 //$NON-NLS-1$ //$NON-NLS-2$
	}

	private int 				fCounter= 0;
	private TextPresentation 	fTextPresentation;
	private boolean 			fInParagraph= false;
	private int 				fIsPreformattedText = 0;
	private boolean 			fIgnore= false;
	private boolean 			fHeaderDetected= false;
	
	private int 				fBold = 0;
	private int 				fItalic = 0;
	private int					fStrikeout= 0;
	private int					fTextStyle = SWT.NORMAL;
	private int					fLastRegionEnd;
	private Stack<Font>			fFontStack;
	
	private static int BOLD 		= 1;
	private static int ITALIC 		= 2;
	private static int STRIKEOUT 	= 4;
	

	/**
	 * Transforms the HTML text from the reader to formatted text.
	 *
	 * @param reader the reader
	 * @param presentation If not <code>null</code>, formattings will be applied to
	 * the presentation.
	*/
	public HTML2TextReader(Reader reader, TextPresentation presentation) {
		super(new PushbackReader(reader));
		fTextPresentation= presentation;
		fFontStack = new Stack<Font>();
	}

	public int read() throws IOException {
		int c= super.read();
		if (c != -1) {
	//		fCounter++;
		}
		return c;
	}
	
	@Override
	public String getString() throws IOException {
		StringBuilder sb = new StringBuilder();
		int ch;
		
		while ((ch = read()) != -1) {
			sb.append((char)ch);
			fCounter = sb.length();
		}
	
		return sb.toString();
	}

	private void setTextAttr(int attr) {
		int old_style = fTextStyle;
		
		if ((attr & BOLD) != 0) {
			fBold++;
		}
	
		if ((attr & ITALIC) != 0) {
			fItalic++;
		}
		
		if ((attr & STRIKEOUT) != 0) {
			fStrikeout++;
		}

		fTextStyle = 
				((fBold>0)?BOLD:0) +
				((fItalic>0)?ITALIC:0) +
				((fStrikeout>0)?STRIKEOUT:0);
		
		if (old_style != fTextStyle && fCounter != fLastRegionEnd) {
			// Apply the 'old' style to the previous region
			applyStyleRegion(old_style, currFont());
		}
	}
	
	private void clrTextAttr(int attr) {
		int old_style = fTextStyle;
		
		if ((attr & BOLD) != 0) {
			if (fBold > 0) {
				fBold--;
			}
		}
	
		if ((attr & ITALIC) != 0) {
			if (fItalic > 0) {
				fItalic--;
			}
		}
		
		if ((attr & STRIKEOUT) != 0) {
			if (fStrikeout > 0) {
				fStrikeout--;
			}
		}

		fTextStyle = 
				((fBold>0)?BOLD:0) +
				((fItalic>0)?ITALIC:0) +
				((fStrikeout>0)?STRIKEOUT:0);
		
		if (old_style != fTextStyle && fCounter != fLastRegionEnd) {
			// Apply the 'old' style to the previous region
			applyStyleRegion(old_style, currFont());
		}
	}
	
	private void setFont(Font font) {
		Font old_font = currFont();
		fFontStack.push(font);
		
		if (old_font != currFont() && fCounter != fLastRegionEnd) {
			// Apply the 'old' style to the previous region
			applyStyleRegion(fTextStyle, old_font);
		}
	}
	
	private void clrFont() {
		Font old_font = currFont();
		if (fFontStack.size() > 0) {
			fFontStack.pop();
		}
		
		if (old_font != currFont() && fCounter != fLastRegionEnd) {
			applyStyleRegion(fTextStyle, old_font);
		}
	}
	
	private Font currFont() {
		if (fFontStack.size() > 0) {
			return fFontStack.peek();
		} else {
			return null;
		}
	}
	
	private void applyStyleRegion(int text_style, Font font) {
		int offset = fLastRegionEnd;
		int length = (fCounter-fLastRegionEnd);

		if (fTextPresentation != null && offset >= 0 && length > 0) {
			StyleRange range = new StyleRange(offset, length, null, null);
			if ((text_style & BOLD) != 0) {
				range.fontStyle += SWT.BOLD;
			}
			if ((text_style & ITALIC) != 0) {
				range.fontStyle += SWT.ITALIC;
			}
			if ((text_style & STRIKEOUT) != 0) {
				range.strikeout = true;
			}
			
			if (font != null) {
				range.font = font;
			}
		
			fTextPresentation.addStyleRange(range);
		}
		fLastRegionEnd = fCounter;
	}

	/*
	private void setBold(int offset, int length) {
		if (fTextPresentation != null && offset >= 0 && length > 0) {
			fTextPresentation.addStyleRange(new StyleRange(offset, length, null, null, SWT.BOLD));
		}
	}

	private void setStrikeout(int offset, int length) {
		if (fTextPresentation != null && offset >= 0 && length > 0) {
			StyleRange styleRange= new StyleRange(offset, length, null, null, SWT.NORMAL);
			styleRange.strikeout= true;
			fTextPresentation.addStyleRange(styleRange);
		}
	}

	private void setBoldAndStrikeOut(int offset, int length) {
		if (fTextPresentation != null && offset >= 0 && length > 0) {
			StyleRange styleRange= new StyleRange(offset, length, null, null, SWT.BOLD);
			styleRange.strikeout= true;
			fTextPresentation.addStyleRange(styleRange);
		}
	}

	private void setItalic(int offset, int length) {
		if (fTextPresentation != null && offset >= 0 && length > 0) {
			fTextPresentation.addStyleRange(new StyleRange(offset, length, null, null, SWT.ITALIC));
		}
	}
	 */
	
	protected void startBold() {
		setTextAttr(BOLD);
	
		/*
		if (fBold == 0) {
			fBoldStartOffset= fCounter;
			if (fStrikeout > 0) {
				setStrikeout(fStrikeoutStartOffset, fCounter - fStrikeoutStartOffset);
			}
		}
		++fBold;
		 */
	}

	protected void stopBold() {
		clrTextAttr(BOLD);
		/*
		--fBold;
		if (fBold == 0) {
			if (fStrikeout == 0) {
				setBold(fBoldStartOffset, fCounter - fBoldStartOffset);
			} else {
				setBoldAndStrikeOut(fBoldStartOffset, fCounter - fBoldStartOffset);
				fStrikeoutStartOffset= fCounter;
			}
			fBoldStartOffset= -1;
		}
		 */
	}

	protected void startItalic() {
		setTextAttr(ITALIC);
		/*
		if (fItalic == 0) {
			fItalicStartOffset= fCounter;
			if (fStrikeout > 0) {
				setStrikeout(fStrikeoutStartOffset, fCounter - fStrikeoutStartOffset);
			}
		}
		++fItalic;
		 */
	}

	protected void stopItalic() {
		clrTextAttr(ITALIC);
		/*
		--fItalic;
		if (fItalic == 0) {
			if (fStrikeout == 0) {
				setItalic(fItalicStartOffset, fCounter - fItalicStartOffset);
			} else {
				setBoldAndStrikeOut(fBoldStartOffset, fCounter - fBoldStartOffset);
				fStrikeoutStartOffset= fCounter;
			}
			fItalicStartOffset= -1;
		}
		 */
	}
	
	protected void startStrikeout() {
		setTextAttr(STRIKEOUT);
		/*
		if (fStrikeout == 0) {
			fStrikeoutStartOffset= fCounter;
			if (fBold > 0) {
				setBold(fBoldStartOffset, fCounter - fBoldStartOffset);
			}
		}
		++fStrikeout;
		 */
	}

	protected void stopStrikeout() {
		clrTextAttr(STRIKEOUT);
		/*
		--fStrikeout;
		if (fStrikeout == 0) {
			if (fBold == 0) {
				setStrikeout(fStrikeoutStartOffset, fCounter - fStrikeoutStartOffset);
			} else {
				setBoldAndStrikeOut(fStrikeoutStartOffset, fCounter - fStrikeoutStartOffset);
				fBoldStartOffset= fCounter;
			}
			fStrikeoutStartOffset= -1;
		}
		 */
	}

	protected void startPreformattedText() {
		setFont(JFaceResources.getTextFont());
		fIsPreformattedText++;
		setSkipWhitespace(false);
	}

	protected void stopPreformattedText() {
		clrFont();
		if (fIsPreformattedText > 0) {
			fIsPreformattedText--;
		}
		setSkipWhitespace(true);
	}


	/*
	 * @see org.eclipse.jdt.internal.ui.text.SubstitutionTextReader#computeSubstitution(int)
	 */
	protected String computeSubstitution(int c) throws IOException {
		if (c == '<') {
			return  processHTMLTag();
		} else if (fIgnore) {
			return EMPTY_STRING;
		} else if (c == '&') {
			return processEntity();
		} else if (fIsPreformattedText > 0) {
			return processPreformattedText(c);
		}

		return null;
	}

	private String html2Text(String html) {

		if (html == null || html.length() == 0) {
			return EMPTY_STRING;
		}

		html= html.toLowerCase();
		
		String tag= html;
		if ('/' == tag.charAt(0))
			tag= tag.substring(1);

		if (!fgTags.contains(tag))
			return EMPTY_STRING;


		if ("pre".equals(html)) { //$NON-NLS-1$
			startPreformattedText();
			return EMPTY_STRING;
		}

		if ("/pre".equals(html)) { //$NON-NLS-1$
			stopPreformattedText();
			return EMPTY_STRING;
		}

		if (fIsPreformattedText > 0) {
			return EMPTY_STRING;
		}

		if ("b".equals(html)) { //$NON-NLS-1$
			startBold();
			return EMPTY_STRING;
		}
		
		if ("i".equals("html")) {
			startItalic();
			return EMPTY_STRING;
		}

		if ("del".equals(html)) { //$NON-NLS-1$
			startStrikeout();
			return EMPTY_STRING;
		}

		if ((html.length() > 1 && html.charAt(0) == 'h' && Character.isDigit(html.charAt(1))) || "dt".equals(html)) { //$NON-NLS-1$
			startBold();
			return EMPTY_STRING;
		}

		if ("dl".equals(html)) //$NON-NLS-1$
			return LINE_DELIM;

		if ("dd".equals(html)) //$NON-NLS-1$
			return "\t"; //$NON-NLS-1$

		if ("li".equals(html)) //$NON-NLS-1$
			// FIXME: this hard-coded prefix does not work for RTL languages, see https://bugs.eclipse.org/bugs/show_bug.cgi?id=91682
//			return LINE_DELIM + HTMLMessages.getString("HTML2TextReader.listItemPrefix"); //$NON-NLS-1$
			return LINE_DELIM + "\t-";

		if ("/b".equals(html)) { //$NON-NLS-1$
			stopBold();
			return EMPTY_STRING;
		}
		
		if ("/i".equals(html)) {
			stopItalic();
			return EMPTY_STRING;
		}

		if ("/del".equals(html)) { //$NON-NLS-1$
			stopStrikeout();
			return EMPTY_STRING;
		}

		if ("p".equals(html))  { //$NON-NLS-1$
			fInParagraph= true;
			return LINE_DELIM;
		}

		if ("br".equals(html) || "br/".equals(html) || "div".equals(html)) //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			return LINE_DELIM;

		if ("/p".equals(html))  { //$NON-NLS-1$
			boolean inParagraph= fInParagraph;
			fInParagraph= false;
			return inParagraph ? EMPTY_STRING : LINE_DELIM;
		}

		if ((html.startsWith("/h") && html.length() > 2 && Character.isDigit(html.charAt(2))) || "/dt".equals(html)) { //$NON-NLS-1$ //$NON-NLS-2$
			stopBold();
			return LINE_DELIM;
		}

		if ("/dd".equals(html)) //$NON-NLS-1$
			return LINE_DELIM;
		// End of list... add \n
		if ("/ul".equals(html)) //$NON-NLS-1$
			return LINE_DELIM;
		
		if ("head".equals(html) && !fHeaderDetected) { //$NON-NLS-1$
			fHeaderDetected= true;
			fIgnore= true;
			return EMPTY_STRING;
		}

		if ("/head".equals(html) && fHeaderDetected && fIgnore) { //$NON-NLS-1$
			fIgnore= false;
			return EMPTY_STRING;
		}

		return EMPTY_STRING;
	}

	/*
	 * A '<' has been read. Process a html tag
	 */
	private String processHTMLTag() throws IOException {

		StringBuffer buf= new StringBuffer();
		int ch;
		do {

			ch= nextChar();

			while (ch != -1 && ch != '>') {
				buf.append(Character.toLowerCase((char) ch));
				ch= nextChar();
				if (ch == '"'){
					buf.append(Character.toLowerCase((char) ch));
					ch= nextChar();
					while (ch != -1 && ch != '"'){
						buf.append(Character.toLowerCase((char) ch));
						ch= nextChar();
					}
				}
				if (ch == '<' && !isInComment(buf)) {
					unread(ch);
					return '<' + buf.toString();
				}
			}

			if (ch == -1)
				return null;

			if (!isInComment(buf) || isCommentEnd(buf)) {
				break;
			}
			// unfinished comment
			buf.append((char) ch);
		} while (true);

		return html2Text(buf.toString());
	}

	private static boolean isInComment(StringBuffer buf) {
		return buf.length() >= 3 && "!--".equals(buf.substring(0, 3)); //$NON-NLS-1$
	}

	private static boolean isCommentEnd(StringBuffer buf) {
		int tagLen= buf.length();
		return tagLen >= 5 && "--".equals(buf.substring(tagLen - 2)); //$NON-NLS-1$
	}

	private String processPreformattedText(int c) {
		if  (c == '\r' || c == '\n')
			fCounter++;
		return null;
	}


	private void unread(int ch) throws IOException {
		((PushbackReader) getReader()).unread(ch);
	}

	protected String entity2Text(String symbol) {
		if (symbol.length() > 1 && symbol.charAt(0) == '#') {
			int ch;
			try {
				if (symbol.charAt(1) == 'x') {
					ch= Integer.parseInt(symbol.substring(2), 16);
				} else {
					ch= Integer.parseInt(symbol.substring(1), 10);
				}
				return EMPTY_STRING + (char)ch;
			} catch (NumberFormatException e) {
			}
		} else {
			String str= (String) fgEntityLookup.get(symbol);
			if (str != null) {
				return str;
			}
		}
		return "&" + symbol; // not found //$NON-NLS-1$
	}

	/*
	 * A '&' has been read. Process a entity
	 */
	private String processEntity() throws IOException {
		StringBuffer buf= new StringBuffer();
		int ch= nextChar();
		while (Character.isLetterOrDigit((char)ch) || ch == '#') {
			buf.append((char) ch);
			ch= nextChar();
		}

		if (ch == ';')
			return entity2Text(buf.toString());

		buf.insert(0, '&');
		if (ch != -1)
			buf.append((char) ch);
		return buf.toString();
	}
}
