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

import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultIndentLineAutoEditStrategy;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;

public class SVAutoIndentStrategy extends DefaultIndentLineAutoEditStrategy 
	implements IPropertyChangeListener {
	
	private LogHandle					fLog;
	private boolean						fAutoIndentEnabled;
	
	public SVAutoIndentStrategy(SVEditor editor, String p) {
		fLog = LogFactory.getLogHandle("SVAutoIndentStrategy");
		
		fAutoIndentEnabled = SVUiPlugin.getDefault().getPreferenceStore().getBoolean(
				SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S);
	}
	
	public void propertyChange(PropertyChangeEvent event) {
		if (event.getProperty().equals(SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S)) {
			fAutoIndentEnabled = event.getNewValue().toString().equals("true");
		}
	}

	private void indentPastedContent(IDocument doc, DocumentCommand cmd) {
		fLog.debug("indentPastedContent(offset=" + cmd.offset + ")");
		
		try {
			int lineno = doc.getLineOfOffset(cmd.offset);
			if (doc.getLineOffset(lineno) != cmd.offset) {
				// If this is a block copy
//				System.out.println("not a block copy");
				return;
			}
			int line_cnt = 0;
			
			for (int i=0; i<cmd.text.length(); i++) {
				if (cmd.text.charAt(i) == '\n') {
					line_cnt++;
				}
			}
			
			fLog.debug("Document line start=" + lineno);
			
			StringBuilder doc_str = new StringBuilder();
			// Append what's before the
			
			doc_str.append(doc.get(0, cmd.offset));
			doc_str.append(cmd.text);
			doc_str.append(doc.get(
					cmd.offset+cmd.length, 
					(doc.getLength()-(cmd.offset+cmd.length)-1)));
			
			StringBIDITextScanner text_scanner = 
				new StringBIDITextScanner(doc_str.toString());
			
			SVDefaultIndenter indenter = new SVDefaultIndenter();
			SVIndentScanner scanner = new SVIndentScanner(text_scanner);
			
			indenter.init(scanner);
			
			// The goal, here, is to format the entire document
			// with the new text added. Then, extract out the 'new'
			// portion and send it as the modification event
			
			
			try {
				String result = indenter.indent(lineno+1, (lineno+line_cnt));
				cmd.text = result;
			} catch (Exception e) {
			}

			fLog.debug("active line is: " + lineno);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}
	
	private void indentOnKeypress(IDocument doc, DocumentCommand cmd) {
		StringBuilder doc_str = new StringBuilder();
		boolean indent_newline;

		if (cmd.text != null && isLineDelimiter(doc, cmd.text)) {
			indent_newline = true;
		} else if (cmd.text.length() == 1) {
			indent_newline = false;
		} else {
			return;
		}

		try {
			doc_str.append(doc.get(0, cmd.offset));
			doc_str.append(cmd.text);
			
			// If we're moving to a new line, put a dummy statement in place
			// as a marker
			if (indent_newline) {
				doc_str.append("DUMMY STATEMENT;\n");
			}
			
			if (doc.getLength() > (cmd.offset+cmd.length)) {
				doc_str.append(doc.get(
						cmd.offset+cmd.length, 
						(doc.getLength()-(cmd.offset+cmd.length)-1)));
			}
			
			StringBIDITextScanner text_scanner = 
				new StringBIDITextScanner(doc_str.toString());
			
			SVDefaultIndenter indenter = new SVDefaultIndenter();
			SVIndentScanner scanner = new SVIndentScanner(text_scanner);
			
			indenter.init(scanner);
			
			indenter.indent();

			IRegion cmd_line = doc.getLineInformationOfOffset(cmd.offset);
			String indent = null;
    		if (indent_newline) {
        		// Want the indent of the next line
    			indent = indenter.getLineIndent(doc.getLineOfOffset(cmd.offset)+2);
    		} else {
    			// Want indent of this line
    			indent = indenter.getLineIndent(doc.getLineOfOffset(cmd.offset)+1);
    		}
    		
    		if (indent != null) {
    			if (indent_newline) {
    				cmd.text += indent;
    			} else {
    				int n_ws_chars = 0;
    				// replace any leading whitespace with the new indent
    				while ((cmd_line.getOffset()+n_ws_chars) < doc.getLength() &&
    						Character.isWhitespace(
    						doc.getChar(cmd_line.getOffset()+n_ws_chars)) &&
    						doc.getChar(cmd_line.getOffset()+n_ws_chars) != '\n') {
    					n_ws_chars++;
    				}
    				
    				// Only indent in certain cases:
    				// - A closing brace decreases the indent
    				// - The command text completes an end-keyword at the start of the
    				//   line that decreases the indent
    				if (cmd.text.equals("}") && (indent.length() < n_ws_chars)) {
    					doc.replace(cmd_line.getOffset(), n_ws_chars, indent);
    					cmd.offset += (indent.length() - n_ws_chars);
    				} else {
    					int idx = cmd.offset-1, c;
    					doc_str.setLength(0);
    					doc_str.append(cmd.text);
    					while (idx >= 0) {
    						c = doc.getChar(idx);
    						if (!Character.isWhitespace(c)) {
    							doc_str.append((char)c);
    							idx--;
    						} else {
    							break;
    						}
    					}
    					doc_str.reverse();
    					
    					if ((doc_str.toString().startsWith("end") ||
    							doc_str.toString().equals("while") ||
    							doc_str.toString().equals("join") ||
    							doc_str.toString().equals("join_any") ||
    							doc_str.toString().equals("join_none")) 
    						&& (indent.length() < n_ws_chars)) {
        					doc.replace(cmd_line.getOffset(), n_ws_chars, indent);
        					cmd.offset += (indent.length() - n_ws_chars);
    					}
    				}
    			}
    		}
			
		} catch (BadLocationException e) {
			fLog.error("Problem with auto-indent", e);
		}
	}
	
    public void customizeDocumentCommand(IDocument doc, DocumentCommand cmd) {
    	
    	if (!fAutoIndentEnabled) {
    		return;
    	}
    	
    	if (cmd.length == 0) {
    		// adding text
    		indentOnKeypress(doc, cmd);
    	}
    	if (cmd.text.length() > 1) {
    		indentPastedContent(doc, cmd);
    	}
    }

	private boolean isLineDelimiter(IDocument document, String text) {
		String[] delimiters= document.getLegalLineDelimiters();
		if (delimiters != null)
			return TextUtilities.equals(delimiters, text) > -1;
			return false;
	}
	
}
