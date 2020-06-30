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
 *     Steven Dawson - initial implementation
 ****************************************************************************/

package org.eclipse.hdt.sveditor.ui.editor.actions;

import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import org.eclipse.hdt.sveditor.ui.editor.SVDocumentPartitions;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.TextEditorAction;

public class SelectEnclosingElementAction extends TextEditorAction {
	private SVEditor fEditor;
	private static final Map<String, String> fBeginCharMap;
	private static final Map<String, String> fEndCharMap;
	// These fields are used to help derive the direction to search in if we
	// have text selected (presumably from the
	// previous match that we are toggling between
	private LogHandle fLog;

	static {
		fBeginCharMap = new HashMap<String, String>();
		fBeginCharMap.put("(", ")");
		fBeginCharMap.put("{", "}");
		fBeginCharMap.put("[", "]");
		fBeginCharMap.put("begin", "end");
		fBeginCharMap.put("module", "endmodule");
		fBeginCharMap.put("function", "endfunction");
		fBeginCharMap.put("task", "endtask");
		fBeginCharMap.put("class", "endclass");
		fBeginCharMap.put("generate", "endgenerate");
		fBeginCharMap.put("package", "endpackage");
		fBeginCharMap.put("case", "endcase");
		fBeginCharMap.put("clocking", "endclocking");
		fBeginCharMap.put("config", "endconfig");
		fBeginCharMap.put("covergroup", "endgroup");
		fBeginCharMap.put("interface", "endinterface");
		fBeginCharMap.put("primitive", "endprimitive");
		fBeginCharMap.put("program", "endprogram");
		fBeginCharMap.put("property", "endproperty");
		fBeginCharMap.put("specify", "endspecify");
		fBeginCharMap.put("sequence", "endsequence");
		fBeginCharMap.put("table", "endtable");
		fBeginCharMap.put("fork", "join join_none join_any");
	}
	
	static {
		fEndCharMap = new HashMap<String, String>();
		fEndCharMap.put(")", "(");
		fEndCharMap.put("}", "{");
		fEndCharMap.put("]", "[");
		fEndCharMap.put("end", "begin");
		fEndCharMap.put("endmodule", "module");
		fEndCharMap.put("endfunction", "function");
		fEndCharMap.put("endtask", "task");
		fEndCharMap.put("endclass", "class");
		fEndCharMap.put("endgenerate", "generate");
		fEndCharMap.put("endpackage", "package");
		fEndCharMap.put("endcase", "case");
		fEndCharMap.put("endclocking", "clocking");
		fEndCharMap.put("endconfig", "config");
		fEndCharMap.put("endgroup", "covergroup");
		fEndCharMap.put("endinterface", "interface");
		fEndCharMap.put("endprimitive", "primitive");
		fEndCharMap.put("endprogram", "program");
		fEndCharMap.put("endproperty", "property");
		fEndCharMap.put("endspecify", "specify");
		fEndCharMap.put("endsequence", "sequence");
		fEndCharMap.put("endtable", "table");
		fEndCharMap.put("join", "fork");
		fEndCharMap.put("join_none", "fork");
		fEndCharMap.put("join_any", "fork");
	}

	public SelectEnclosingElementAction(ResourceBundle bundle, String prefix,
			SVEditor editor) {
		super(bundle, prefix, editor);
		fEditor = editor;

		fLog = LogFactory.getLogHandle("SVESelectEnclosingElement");

	}

	/**
	 * Rules: - If nothing selected - Not on a word, but within a statement,
	 * select the statement - On a word, select word - Not on a word, select
	 * nearest enclosing statement - If text selected - If starts & ends with
	 * open / close braces - Select enclosing open / close brace - Else - select
	 * word
	 */
	@Override
	public void run() {
		ISourceViewer sv = fEditor.sourceViewer();
		IDocument doc = sv.getDocument();
		ITextSelection tsel = (ITextSelection) fEditor.getSite()
				.getSelectionProvider().getSelection();

		int offset = tsel.getOffset();
		int sel_offset = offset; // save this for later
		int sel_len = tsel.getLength();
		int n_st = 0, n_en = 0;
		// If we have text selected, and we last searched forward, move our
		// cursor to the end of the selection
		// if ((len != 0) && (fLastSearchForward == true)) {

		// Check for end of file
		if (offset >= doc.getLength()) {
			offset = doc.getLength() - 1;
		}
		int start_pos = -1;
		int end_pos = -1;

		try {
			int ch = doc.getChar(offset);
			int prevch = 0;

			// Check for the condition where we are at the end of a word
			if (IsWhitespace(ch) && !IsWhitespace(prevch) && (offset > 0)) {
				// Step back one character into a word
				offset--;
			}

			// Create a scanner
			SVDocumentTextScanner scanner = new SVDocumentTextScanner(doc,
					SVDocumentPartitions.SV_PARTITIONING, new String[] {
							SVDocumentPartitions.SV_MULTILINE_COMMENT,
							SVDocumentPartitions.SV_SINGLELINE_COMMENT,
							SVDocumentPartitions.SV_STRING }, "", offset,
					false, // Start by scanning backwards
					true); // Skip Comments

			// Firstly figure out where we are in the code
			// If we don't have anything selected... check if we are touching a
			// word ... if so select it and return
			if (offset > 0) {
				prevch = doc.getChar(offset - 1);
				start_pos = offset;
				end_pos = offset;
			}

			// If nothing is selected and we are in the middle of no-where
			// - Just select the enclosing element
			// This portion of code will get us to the enclosing start brace
			if ((sel_len == 0) && IsWhitespace(ch) && IsWhitespace(prevch)) {
				// If we have nothing selected, and we are in the middle of some
				// whitespace ... whatever enclosing element we are in
				if (IsWhitespace(ch) && IsWhitespace(prevch)) {
					// Now just search backwards till we find an opening brace
					String tt = "garbage";
					while (!fBeginCharMap.containsKey(tt)) {

						if ((tt = GetNextString(scanner)) == null) {
							// Nothing found ... return
							return;
						}
					}

					// Found a start ... get position and change direction
					SetScannerDirection(scanner, true);
					start_pos = (int) scanner.getPos();
				}
			}
			// Nothing selected ... but we have some non-white space stuff
			// around us
			// See if it is a begin or end statement, if so we need to find
			// a match, else we need to just select the word
			else if (sel_len == 0) {
				// Check if we need to step back a character
				if (IsWhitespace(ch) && IsWhitespace(prevch)) {
					scanner.seek(offset - 1);
				}

				// Next get the word itself that we are busy with
				String tt;
				if ((tt = GetNextString(scanner)) != null) {
					start_pos = (int) scanner.getRealPos() + 1;
					if (start_pos < 0)
						start_pos = 0;
					SetScannerDirection(scanner, true);
					if ((tt = GetNextString(scanner)) != null) {
						end_pos = (int) scanner.getPos();
					} else {
						return;
					}
				} else {
					// Nothing found ... return
					return;
				}

				// Check for start of range, end of range
				if (fBeginCharMap.containsKey(tt)) {
					fLog.debug("Found start key'" + tt + "'");
					n_st = 1;
					// Capture start & end keymaps
					// We have an end-point ... scan forwards
					SetScannerDirection(scanner, true);
				}
				// Check for start of range, end of range
				else if (fEndCharMap.containsKey(tt)) {
					fLog.debug("Found end key'" + tt + "'");
					n_en = 1;
					end_pos = (int) scanner.getPos();
					// Capture start & end keymaps
					// We have an end-point ... scan backwards
					SetScannerDirection(scanner, false);
					// Hop to start of word... so we don't pick this one up
					scanner.seek(start_pos - 1);

				} else {
					MarkRange(sv, start_pos, end_pos);
					return;
				}
			}
			// If we have something selected the JAVA rules appear to be:
			// - If we have a start brace... match the enclosing event
			// - if it isn't a starting brace, match the word at the start of
			// the selection (kinda)
			else {
				scanner.setScanFwd(true); // Haven't scanned yet... don't call
											// direction changer function
				String tt;
				// Check if we are in the middle of a word...
				if (!IsWhitespace(prevch))  {
					// If so ... head to the start of the word before continuing
					// Scan back to start of word
					scanner.setScanFwd(false);		// Start by scanning backwards
					// Scan for word
					if ((tt = GetNextString(scanner)) == null) {
						return;
					}
					SetScannerDirection(scanner, true);
				}
				tt = GetNextString(scanner);
				fLog.debug("Selected - found first word '" + tt + "'");
				// Check if we have a "open brace"
				if (fBeginCharMap.containsKey(tt)) {
					// Let's see if we can find an open brace
					SetScannerDirection(scanner, false);

					// Reset the scanner start location
					scanner.seek(sel_offset - 1);

					// Now just search backwards till we find an opening brace
					n_st = 0;
					n_en = 0;
					// Loop here till we get an extra "open brace"
					while (n_st <= n_en) {
						if ((tt = GetNextString(scanner)) == null) {
							// Nothing found ... return
							return;
						}
						// check for begin or end characters
						if (fBeginCharMap.containsKey(tt)) {
							n_st++;
							fLog.debug("Found begin '" + tt + "' " + n_st
									+ " - " + n_en);
						}
						// check for begin or end characters
						else if (fEndCharMap.containsKey(tt)) {
							n_en++;
							fLog.debug("Found end '" + tt + "' " + n_st + " - "
									+ n_en);
						}

					}

					// We have found the start...
					start_pos = (int) scanner.getPos();
					if (scanner.getPos() != 0)  {		// Don't increment if start of file
						start_pos ++;
					}
					SetScannerDirection(scanner, true);
					n_st = 0;
					n_en = 0;

				} else {
					// Something is selected, but not a start / end ... just select the current word
					scanner.seek(sel_offset);		// Start at the start of the selection
					if (!IsWhitespace(prevch))  {
						// Scan back to start of word
						scanner.setScanFwd(false);		// Start by scanning backwards
						// Scan for word
						if ((tt = GetNextString(scanner)) == null) {
							return;
						}
						SetScannerDirection(scanner, true);
					}
					start_pos = (int) scanner.getPos();
					// Search to end of string
					if ((tt = GetNextString(scanner)) == null) {
						return;
					}
					scanner.unget_ch(0);
					end_pos = (int) scanner.getPos();	// Get end position
					
					// Mark & return
					MarkRange(sv, start_pos, end_pos);

					
				}
			}

			// By the time we get here, the scanner is going to scan till the start and end brace counts match
			do {
				String tt;
				if ((tt = GetNextString(scanner)) == null) {
					// Shouldn't get null ... presumeable we will get a bug
					// report here
					return;
				}
				fLog.debug("Scanning for match '" + tt + "'");

				if (fBeginCharMap.containsKey(tt)) {
					n_st++;
					fLog.debug("Found start '" + tt + "' - " + n_st + " - "
							+ n_en);
				} else if (fEndCharMap.containsKey(tt)) {
					n_en++;
					fLog.debug("Found end '" + tt + "' - " + n_st + " - "
							+ n_en);
				}
			} while (n_st != n_en);

			if (scanner.getScanFwd()) {
				end_pos = (int) scanner.getPos();
			} else {
				start_pos = (int) scanner.getPos();
				// If we aren't at the start of the file, advance the cursor one position
				if (start_pos != 0)  {
					start_pos ++;
				}
			}
			MarkRange(sv, start_pos, end_pos);

		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}

	/**
	 * boolean IsWhitespace (Integer ch)
	 *
	 * Returns true if it is whitespace
	 */
	private boolean IsWhitespace(Integer ch) {
		// If we have whitespace (or end of line) step back 1 character
		if ((ch == (int) ' ') || (ch == (int) '\t') || (ch == (int) '\r')
				|| (ch == (int) '\n')) {
			return (true);
		}
		return (false);
	}

	private boolean MarkRange(ISourceViewer sv, Integer start, Integer end) {
		if (start >= end) {
			return false;
		}
		if (start < 0) {
			start = 0;
		}
		Integer length = end - start;
		sv.setSelectedRange(start, length);
		sv.revealRange(start, 0);
		return true;
	}

	/**
	 * This will scan and get the following word. The scanner will stop at
	 * punctuation, braces etc, forcing me to do extra work every time I use
	 * it...
	 * 
	 * @param scanner
	 * @return
	 */
	private String GetNextString(SVDocumentTextScanner scanner) {
		int ch;
		String t;
		ch = scanner.get_ch();
		if (scanner.getRealPos() < 0) {
			return null;
		}

		while (IsWhitespace(ch)) {
			if ((ch = scanner.get_ch()) == -1) {
				return null;
			}
		}
		//
		// Skip over strings
		if (ch == '\"') {
			t = scanner.readString(ch);
		}
		// Check if we have an identifier
		else if ((t = scanner.readIdentifier(ch)) == null) {
			// If not, have some sort of special case... handle it
			t = "" + (char) ch;
			if ((ch = scanner.get_ch()) == -1) {
				return (null);
			}
		}

		fLog.debug("Got string '" + t + "'");
		return (t);

	}

	/**
	 * This is used to change direction ... the scanner cursor needs to be moved
	 * if we change dir
	 * 
	 * @param scanner
	 * @return
	 */
	private void SetScannerDirection(SVDocumentTextScanner scanner,
			boolean scan_forward) {
		// Check if we are already pointed in the right direction
		if (scanner.getScanFwd() == scan_forward) {
			// do nothing if so ... and return
			return;
		}
		else  {
			// Scanner will have advanced already, undo it unless we are already at the start of the file
			if (scanner.getPos() > 0)
				scanner.unget_ch(0);
		}

		// Change of direction required
		scanner.setScanFwd(scan_forward);
	}

}
