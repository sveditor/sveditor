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
 *	 Matthew Ballance - initial implementation
 ****************************************************************************/
package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVDefaultIndenter2;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.ILogListener;
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
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;

public class SVAutoIndentStrategy extends DefaultIndentLineAutoEditStrategy 
	implements IPropertyChangeListener, ILogLevelListener {
	
	private LogHandle					fLog;
	private boolean						fDebugEn;
	private boolean						fAutoIndentEnabled;
	private SVEditor					editor; 
	
	public SVAutoIndentStrategy(SVEditor editor, String p) {
		fLog = LogFactory.getLogHandle("SVAutoIndentStrategy");
		logLevelChanged(fLog);
		this.editor = editor;
		
		fAutoIndentEnabled = SVUiPlugin.getDefault().getPreferenceStore().getBoolean(
				SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S);
	}

	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = (fLog.getDebugLevel() > 0);
	}



	public void propertyChange(PropertyChangeEvent event) {
		if (event.getProperty().equals(SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S)) {
			fAutoIndentEnabled = event.getNewValue().toString().equals("true");
		}
	}

	/**
	 * Algorithmically this function works as follows:
	 * - If there are no \n's in the pasted data, just insert it and return
	 * - If there are multiple lines in the pasted data:
	 *   - Insert the pasted data.
	 *   - Run the indenter
	 *   Post-process as follows to match Java behavior
	 *   - If the insertion point is before the start of code on a line, whitespace between the
	 *     insertion point and SOL is replaced by the indenter
	 *     - Any whitespace between the IP and start of code is preserved
	 *   - If pasting after code has started, whitespace on the starting line is not affected.
	 *     - The whitespace on the starting line is used as a reference for pasted code (will 
	 *     align from there)
	 *   
	 *   - All code after the insertion point is preserved, regardless
	 *   
	 * @param doc
	 * @param cmd
	 */
	private void indentPastedContent(IDocument doc, DocumentCommand cmd) {
		fLog.debug("indentPastedContent(offset=" + cmd.offset + ")");
		fLog.debug("	content=\"" + cmd.text + "\"");

		try {
			int lineno = doc.getLineOfOffset(cmd.offset)+1;		// Add 1 because getLineOfOffset starts counting at 0, where lineno will will be used where the first line is line 1
			int target_lineno = lineno;							// Line no determines where we are going to take the indent for the pasted lines from
			boolean added_extra_cr = false;

			int line_cnt = 0, result_line_cnt = 0;
			boolean paste_inside_code = false;		// The insertion point has code before it on the line
			int distance_to_sol = 0;			// used when inserting at the start of a new line, need to remove this WS because indenter will have calculated correct WS
			int ws_at_sol = 0;					// leading whitespace count on the line we are pasting at
			int trailing_whitespace = 0;		// number of WS characters after last \n
			
			// This section checks to see if the document contains any leading whitespace to the left of 
			// the insertion point
			for (int i=cmd.offset-1; i>=0; i--) {
				char current_ch = doc.getChar(i);
				distance_to_sol ++;
				// reached end the end of he previous line ... break out
				if ((current_ch == '\r') || (current_ch == '\n'))  {
					distance_to_sol--;
					break;
				}
				// If we have a space or tab... we want to remove it
				else if ((current_ch == ' ') || (current_ch == '\t'))  {
					ws_at_sol ++;
				}
				// non-white space characters... is an inline paste
				else  {
					ws_at_sol = 0;
					paste_inside_code = true;
				}
			}
			
			// Figure out how many lines are in the pasted text... need to copy these many lines out of the re-formatted data
			for (int i=0; i<cmd.text.length(); i++) {
				// Keep track of number of characters to first \n in pasted code
				if (cmd.text.charAt(i) == '\n' || cmd.text.charAt(i) == '\r') {
					trailing_whitespace = 0;
					if (i+1 < cmd.text.length() &&
							cmd.text.charAt(i) == '\r' &&
							cmd.text.charAt(i+1) == '\n') {
						i++;
					}
					line_cnt++;
				}
				// Increment the number of whitespace characters found after a \n, these need to be trimmed
				else if ((trailing_whitespace > -1) && (cmd.text.charAt(i) == ' ' || cmd.text.charAt(i) == '\t'))  {
					trailing_whitespace ++;
				}
				// Regular character ... -1 shows no trailing
				else  {
					trailing_whitespace = -1;
				}
			}
			
			// Don't indent if pasted code is not multi-line and we aren't in the leading whitespace area of the line 
			if ((line_cnt == 0) && (paste_inside_code == true)) {
				return;
			}
			
			// If the pasted text doesn't end with a CR, then dummy up
			// an extra line which we will remove at the end
			// This will make it easier to extract the text from the indented code
			// at the end
			if (cmd.text.charAt(cmd.text.length()-1) != '\n' &&
					cmd.text.charAt(cmd.text.length()-1) != '\r') {
				line_cnt++;
				added_extra_cr = true;
				cmd.text = cmd.text + "\n";
			}
			
			/**
			 * target_lineno - Determine which line to get the indent from
			 * 
			 * At this point points to the line we are pasting into
			 * If we are pasting before code starts on the line:
			 *   - Take indent from previous line
			 * If we are pasting AFTER code starts on the line:
			 *   - Take indent from line being pasted into
			 */
			if (paste_inside_code == false)  {
				target_lineno --;
			}
			
			// Create a string containing the inserted code
			StringBuilder doc_str = new StringBuilder();

			doc_str.append(doc.get(0, cmd.offset));	// Append what's before the pasted code
			doc_str.append(cmd.text);				// Add the pasted code
			int start = cmd.offset+cmd.length;

			// append the remaining code ... not quite sure if we need this
			int len = (doc.getLength()-(cmd.offset+cmd.length)-1);
			try {
				if (len > 0) {
					doc_str.append(doc.get(start, len));
				}
			} catch (BadLocationException e) {
				System.out.println("[ERROR] start=" + start + " len=" + len + " length=" + doc.getLength());
				throw e;
			}
			
			// Indent on the code
			StringBIDITextScanner text_scanner = 
				new StringBIDITextScanner(doc_str.toString());
			
			fLog.debug("    doc_str:\n" + doc_str.toString());
			
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			SVIndentScanner scanner = new SVIndentScanner(text_scanner);
			
			indenter.init(scanner);
			
			indenter.setAdaptiveIndent(true);
			indenter.setAdaptiveIndentEnd(target_lineno);
			indenter.setIndentIncr(SVUiPlugin.getDefault().getIndentIncr());
	
			// The goal, here, is to format the entire document
			// with the new text added. Then, extract out the 'new'
			// portion and send it as the modification event
			try {
				fLog.debug("    lineno=" + lineno + "    line_cnt=" + line_cnt + " target_lineno=" + target_lineno);
				String result;
				result = indenter.indent(lineno, (lineno+(line_cnt-1)));
				
				for (int i=0; i<result.length(); i++) {
					if (result.charAt(i) == '\n' || result.charAt(i) == '\r') {
						if (i+1 < result.length() && 
								result.charAt(i) == '\r' &&
								result.charAt(i+1) == '\n') {
							i++;
						}
						result_line_cnt++;
					}
				}
				
				// If we changed the line count, then just
				// go with what the user pasted, else use the updated code
				// else cmd.txt is returned, unchanged
				if (result_line_cnt == line_cnt)  {
 					if (added_extra_cr)  {
						// Remove the trailing \n
						result =  result.substring(0,result.length()-1);
					}
 					
					// Remove any trailing whitespace in the cmd
 					if (trailing_whitespace > 0)  {
 						result = result.substring(0, result.length()-trailing_whitespace);
 						result = result + indenter.getLineIndent(lineno+line_cnt-2);
 					}
 					
 					
 					// 
 					// Strip out the original code, if we are pasting somewhere in code, this code is already in the file
					if (paste_inside_code == true)  {
						result = result.substring(distance_to_sol, result.length());
					}
					cmd.text = result;
					
					fLog.debug("    Modifying offset by " + distance_to_sol + 
							" setting cmd.text=\"" + result + "\"");
					
					// If we are pasting within the whitespace before the start of code on this line, need to strip the existing whitespace from the document
					// as this has been replaced by the indenter
					if (!paste_inside_code && (ws_at_sol > 0))  {
						doc.replace(cmd.offset-ws_at_sol, ws_at_sol, "");			// Strip the whitespace
						cmd.offset -= ws_at_sol;						// Move the cursor back by WS characters
					}
				}
			} catch (Exception e) {
				e.printStackTrace();
			}

			fLog.debug("active line is: " + lineno);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		
	}
	
	private void indentOnKeypress(IDocument doc, DocumentCommand cmd) {
		StringBuilder doc_str = new StringBuilder();
		boolean indent_newline = false;
		boolean is_closebrace = false;
		boolean indent_on_tab = false;
		
		if (cmd.text != null && isLineDelimiter(doc, cmd.text)) {
			indent_newline = true;
		// We have entered a '\t' at the start of a newline
		} else if (cmd.text != null && cmd.text.equals("\t"))  {
			try {
				// Search for 2 line-endings back-to-back
				if ((cmd.offset > 0) && doc.getChar(cmd.offset-1) == '\n')  {
					indent_on_tab = true;
					cmd.text = "";
				}
			} catch (BadLocationException e) { }
		} else if (SVDefaultIndenter2.is_close_brace(cmd.text) && 
				is_beginning_of_line(doc, cmd.offset)) {
			is_closebrace = true;
		} else if (cmd.text.length() == 1) {
			indent_newline = false;
		} else {
			// If the actual text is longer than 1, then it's pretty likely
			// that the editor is trying (nicely) to expand tabs for us
			if (cmd.text.length() > 1 && cmd.text.trim().equals("")) {
				String incr = SVUiPlugin.getDefault().getIndentIncr();
				if (!incr.equals("\t")) {
					int indent_len = incr.length();
					if ((cmd.text.length() % indent_len) != 0) {
						int new_mul = (cmd.text.length() / indent_len) + 1;
						String new_text = "";
						for (int i=0; i<new_mul; i++) {
							new_text += incr;
						}
						cmd.text = new_text;
					}
				}
			}
			return;
		}

		try {
			int target_lineno = doc.getLineOfOffset(cmd.offset);
			doc_str.append(doc.get(0, cmd.offset));
			doc_str.append(cmd.text);
			
			// If we're moving to a new line, put a dummy statement in place
			// as a marker
			if (indent_newline || indent_on_tab) {
				if (fDebugEn) {
					fLog.debug("indent_newline | indent_on_tab");
				}
				doc_str.append("DUMMY=5;\n");
			} else if (is_closebrace) {
				doc_str.append(";\n");
				doc_str.append("DUMMY=5;\n");
			}
			
			if (doc.getLength() > (cmd.offset+cmd.length)) {
				doc_str.append(doc.get(
						cmd.offset+cmd.length, 
						(doc.getLength()-(cmd.offset+cmd.length)-1)));
			}
			
			StringBIDITextScanner text_scanner = 
				new StringBIDITextScanner(doc_str.toString());
			
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			SVIndentScanner scanner = new SVIndentScanner(text_scanner);
			
			
			// Determine the appropriate indent increment
			indenter.setIndentIncr(SVUiPlugin.getDefault().getIndentIncr());
			indenter.init(scanner);
			indenter.setAdaptiveIndent(true);
			
			if (indent_newline) {
				target_lineno++;
				fLog.debug("target_lineno=" + target_lineno);
			} else if (is_closebrace) {
				// A close brace
				target_lineno--;
			}
			
			indenter.setAdaptiveIndentEnd(target_lineno);
			String ind_result = indenter.indent();		// ind_result used, but we need to do the indent, and capturing result is useful for debug
			
			IRegion cmd_line = doc.getLineInformationOfOffset(cmd.offset);
			String indent = null;
			if (indent_newline) {
				// Want the indent of the next line
				int line_offset = doc.getLineOfOffset(cmd.offset);
				indent = indenter.getLineIndent(line_offset+2);
			} else if (indent_on_tab) {
					// Want the indent of current
					int line_offset = doc.getLineOfOffset(cmd.offset);
					indent = indenter.getLineIndent(line_offset+1);
			} else {
				// Want indent of this line
				indent = indenter.getLineIndent(doc.getLineOfOffset(cmd.offset)+1);
			}
			
			if (indent != null) {
				if (indent_newline || indent_on_tab) {
					fLog.debug("Indented Content:\n" +
							indenter.indent());
					fLog.debug("indent=\"" + indent + "\"");
					cmd.text += indent;
					// Increment the cmd.length by the amount of leading whitespace. This
					// causes the correct amount of leading whitespace (as determined by 
					// the indenter) to be added to the start of the line.
					// 
					// This case occurs when the user adds a new-line in the middle of
					// leading whitespace for the line.
					int idx = cmd.offset;
					while (idx < doc.getLength() && 
							(doc.getChar(idx) != '\r' && doc.getChar(idx) != '\n') &&
							Character.isWhitespace(doc.getChar(idx))) {
						cmd.length++;
						idx++;
					}
				} else {
					int n_ws_chars = 0;
					// replace any leading whitespace with the new indent
					while ((cmd_line.getOffset()+n_ws_chars) < doc.getLength() &&
							Character.isWhitespace(doc.getChar(cmd_line.getOffset()+n_ws_chars)) &&
							(doc.getChar(cmd_line.getOffset()+n_ws_chars) != '\n' &&
									doc.getChar(cmd_line.getOffset()+n_ws_chars) != '\r')) {
						n_ws_chars++;
					}
					
					// Only indent in certain cases:
					// - A closing brace decreases the indent
					// - The command text completes an end-keyword at the start of the
					//   line that decreases the indent
					if ((cmd.text.equals("{") || cmd.text.equals("}") || cmd.text.equals(")")) && (indent.length() < n_ws_chars)) {
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
						// unindent the following if typed
						if ((doc_str.toString().startsWith("end") ||
								doc_str.toString().equals("begin") ||
								doc_str.toString().equals("while") ||
								doc_str.toString().equals("join") ||
								doc_str.toString().equals("join_any") ||
								doc_str.toString().equals("join_none") ||
								doc_str.toString().equals("`else") ||
								doc_str.toString().equals("`endif")
								) 
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
	
	private boolean is_beginning_of_line(IDocument doc, int offset) {
		boolean ret = false;
		try {
			for (int i=offset-1; i>=0; i--) {
				if (doc.getChar(i) == '\n') {
					ret = true;
					break;
				} else if (!Character.isWhitespace(doc.getChar(i))) {
					break;
				}
			}
			
		} catch (BadLocationException e) { }
		
		return ret;
	}
	
	public void customizeDocumentCommand(IDocument doc, DocumentCommand cmd) {
		if (!fAutoIndentEnabled) {
			return;
		}
		// Normally, cmd.text.length will be 1 (character typed). 
		// When tab==spaces, however, cmd.text will contain a 
		// series of spaces
		if (cmd.length == 0 && cmd.text.trim().length() <= 1) {
			// adding text
			indentOnKeypress(doc, cmd);
		} else if (cmd.text.length() > 1) {
			indentPastedContent(doc, cmd);
		}
	}

	private boolean isLineDelimiter(IDocument document, String text) {
		String[] delimiters= document.getLegalLineDelimiters();
		if (delimiters != null) {
			return TextUtilities.equals(delimiters, text) > -1;
		}
		return false;
	}
}
