/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.editor.actions;

import java.util.HashMap;
import java.util.Map;
import java.util.ResourceBundle;

import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.ui.editor.SVDocumentPartitions;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.TextEditorAction;

public class GotoMatchingBracketAction extends TextEditorAction {
	private SVEditor fEditor;
	private static final Map<String, String[]> fBeginCharMap;
	private static final Map<String, String[]> fEndCharMap;

	static {
		fBeginCharMap = new HashMap<String, String[]>();
		fBeginCharMap.put("("        , new String [] {")"});
		fBeginCharMap.put("{"        , new String [] {"}"});
		fBeginCharMap.put("["        , new String [] {"]"});
		fBeginCharMap.put("begin"    , new String [] {"end"});
		fBeginCharMap.put("module"   , new String [] {"endmodule"});
		fBeginCharMap.put("function" , new String [] {"endfunction"});
		fBeginCharMap.put("task"     , new String [] {"endtask"});
		fBeginCharMap.put("class"    , new String [] {"endclass"});
		fBeginCharMap.put("generate" , new String [] {"endgenerate"});
		fBeginCharMap.put("package"  , new String [] {"endpackage"});
		fBeginCharMap.put("case"     , new String [] {"endcase"});
		fBeginCharMap.put("clocking" , new String [] {"endclocking"});
		fBeginCharMap.put("config"   , new String [] {"endconfig"});
		fBeginCharMap.put("group"    , new String [] {"endgroup"});
		fBeginCharMap.put("interface", new String [] {"endinterface"});
		fBeginCharMap.put("primitive", new String [] {"endprimitive"});
		fBeginCharMap.put("program"  , new String [] {"endprogram"});
		fBeginCharMap.put("property" , new String [] {"endproperty"});
		fBeginCharMap.put("specify"  , new String [] {"endspecify"});
		fBeginCharMap.put("sequence" , new String [] {"endsequence"});
		fBeginCharMap.put("table"    , new String [] {"endtable"});
		fBeginCharMap.put("fork"     , new String [] {"join", "join_any", "join_none"});
	}
	static {
		fEndCharMap = new HashMap<String, String[]>();
		fEndCharMap.put(")"            , new String [] {"("});
		fEndCharMap.put("}"            , new String [] {"{"});
		fEndCharMap.put("]"            , new String [] {"["});
		fEndCharMap.put("end"          , new String [] {"begin"});
		fEndCharMap.put("endmodule"    , new String [] {"module"});
		fEndCharMap.put("endfunction"  , new String [] {"function"});
		fEndCharMap.put("endtask"      , new String [] {"task"});
		fEndCharMap.put("endclass"     , new String [] {"class"});
		fEndCharMap.put("endgenerate"  , new String [] {"generate"});
		fEndCharMap.put("endpackage"   , new String [] {"package"});
		fEndCharMap.put("endcase"      , new String [] {"case"});
		fEndCharMap.put("endclocking"  , new String [] {"clocking"});
		fEndCharMap.put("endconfig"    , new String [] {"config"});
		fEndCharMap.put("endgroup"     , new String [] {"group"});
		fEndCharMap.put("endinterface" , new String [] {"interface"});
		fEndCharMap.put("endprimitive" , new String [] {"primitive"});
		fEndCharMap.put("endprogram"   , new String [] {"program"});
		fEndCharMap.put("endproperty"  , new String [] {"property"});
		fEndCharMap.put("endspecify"   , new String [] {"specify"});
		fEndCharMap.put("endsequence"  , new String [] {"sequence"});
		fEndCharMap.put("endtable"     , new String [] {"table"});
		fEndCharMap.put("join"         , new String [] {"fork"});
		fEndCharMap.put("join_none"    , new String [] {"fork"});
		fEndCharMap.put("join_any"     , new String [] {"fork"});
	}

	public GotoMatchingBracketAction(ResourceBundle bundle, String prefix,
			SVEditor editor) {
		super(bundle, prefix, editor);
		fEditor = editor;

	}

	@Override
	public void run() {
		ISourceViewer sv = fEditor.sourceViewer();
		IDocument doc = sv.getDocument();
		ITextSelection tsel = (ITextSelection) fEditor.getSite()
				.getSelectionProvider().getSelection();

		int offset = tsel.getOffset();
		int len = tsel.getLength();

		// Check for end of file
		if (offset >= doc.getLength()) {
			offset = doc.getLength() - 1;
		}
		// Save the original offset for later
		int sel_offset = offset;

		String st = "undefined";
		String [] en = null;
		boolean begin = false;
		boolean valid = false;
		int start_pos = -1;
		int end_pos = -1;

		try {
			int ch = doc.getChar(offset);
			int prevch = 0;
			if (offset > 0) {
				prevch = doc.getChar(offset - 1);
			}

			// If we have whitespace (or end of line) step back 1 character
			// This will allow us to jump between begin & end with out moving
			// the cursor
			if ((ch == (int) ' ') || (ch == (int) '\t') || (ch == (int) '\r')
					|| (ch == (int) '\n') || (ch == -1)) {
				offset--;
				ch = doc.getChar(offset);
				if (offset > 0) {
					prevch = doc.getChar(offset - 1);
				}
			}

			// Convert this character to a string and start searching
			String st_c = "" + (char) ch;
			String prev_st_c = "" + (char) prevch;
			// Search for normal open brace ([{
			if (fBeginCharMap.containsKey(st_c)) {
				begin = true;
				st = st_c;
				en = fBeginCharMap.get(st_c);
				start_pos = offset;
				offset++;
				valid = true;
				// Search for normal close brace (]}
			} else if (fEndCharMap.containsKey(st_c)) {
				begin = false;
				st = st_c;
				en = fEndCharMap.get(st_c);
				valid = true;
				start_pos = offset + 1;
				offset--;
				// Search for normal open brace ([{
			} else if (fBeginCharMap.containsKey(prev_st_c)) {
				begin = true;
				st = st_c;
				en = fBeginCharMap.get(prev_st_c);
				valid = true;
				start_pos = offset - 1;
				// Search for normal close brace (]}
			} else if (fEndCharMap.containsKey(prev_st_c)) {
				begin = false;
				st = st_c;
				en = fEndCharMap.get(prev_st_c);
				valid = true;
				start_pos = offset;
				offset -= 2;
				// Failing these, start searching for begin/end which means we
				// have to build up words
			} else {
				// Scan the characters around the carat
				int st_off = offset;
				int en_off = offset;

				do {
					ch = doc.getChar(st_off);

					if (!SVCharacter.isSVIdentifierPart(ch)) {
						break;
					}
					st_off--;
				} while (st_off >= 0);

				if (st_off < 0) {
					st_off = 0;
				} else if (st_off < offset) {
					st_off++;
				}

				do {
					ch = doc.getChar(en_off);

					if (!SVCharacter.isSVIdentifierPart(ch)) {
						break;
					}
					en_off++;
				} while (en_off < doc.getLength());

				if (en_off > offset) {
					en_off--;
				}

				if (en_off > st_off) {
					String str = doc.get(st_off, (en_off - st_off + 1));

					if (fBeginCharMap.containsKey(str)) {
						st = str;
						en = fBeginCharMap.get(str);
						offset = en_off + 1;
						begin = true;
						valid = true;
						start_pos = offset;
					} else if (fEndCharMap.containsKey(str)) {
						st = str;
						en = fEndCharMap.get(str);
						offset = st_off - 1;
						begin = false;
						valid = true;
						start_pos = offset;
					}
				}
			}

			if (valid) {
				SVDocumentTextScanner scanner = new SVDocumentTextScanner(doc,
						SVDocumentPartitions.SV_PARTITIONING, new String[] {
								SVDocumentPartitions.SV_MULTILINE_COMMENT,
								SVDocumentPartitions.SV_SINGLELINE_COMMENT,
								SVDocumentPartitions.SV_STRING }, "", offset,
						begin, true);

				int n_st = 1, n_en = 0;

				do {
					if ((ch = scanner.get_ch()) == -1) {
						break;
					}

					String t;
					if (ch == '\"') {
						t = scanner.readString(ch);
					} else if ((t = scanner.readIdentifier(ch)) == null) {
						scanner.get_ch();
						t = "" + (char) ch;
					}

					if (t.equals(st)) {
						n_st++;
					} else {
						// Loop through all items in en checking for the keyword
						for (String f_en : en)  {
							if (t.equals(f_en)) {
								n_en++;
								break;
							}
						}
					}
				} while (n_st != n_en);

				if (n_st == n_en) {
					int pos = (int) scanner.getPos();

					if (!begin) {
						pos++;
					}
					end_pos = pos;

					int length = 0;
					if ((start_pos != -1) && (end_pos != -1)) {
						// If text was selected when the operation was
						// triggered,
						// extend the selection
						if (len > 0) {
							if (len != 0 && !begin) {
								sel_offset += len;
							}
							if (sel_offset >= doc.getLength()) {
								sel_offset = doc.getLength() - 1;
							}

							length = end_pos - sel_offset;
							sv.setSelectedRange(sel_offset, length);
						} else {
							// Otherwise, just move the cursor
							sv.setSelectedRange(pos, 0);
						}
					} else {
						sv.setSelectedRange(pos, 0);
					}

					sv.revealRange(pos, 0);
				}
			}
		} catch (BadLocationException e) {
		}
	}

}
