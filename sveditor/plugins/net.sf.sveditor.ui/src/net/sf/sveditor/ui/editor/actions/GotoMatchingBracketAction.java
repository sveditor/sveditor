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
	private SVEditor				fEditor;
	private Map<String, String>		fBeginCharMap;
	private Map<String, String>		fEndCharMap;
	// These fields are used to help derive the direction to search in if we have text selected (presumeably from the
	// previous match that we are toggling between
	private boolean					fLastSearchForward = false;
	
	public GotoMatchingBracketAction(ResourceBundle bundle, String prefix, SVEditor editor) {
		super(bundle, prefix, editor);
		fEditor = editor;
		fBeginCharMap = new HashMap<String, String>();
		fBeginCharMap.put("(", ")");
		fBeginCharMap.put("{", "}");
		fBeginCharMap.put("[", "]");
		fBeginCharMap.put("begin"    , "end"        );
		fBeginCharMap.put("module"   , "endmodule"  );
		fBeginCharMap.put("function" , "endfunction");
		fBeginCharMap.put("task"     , "endtask"    );
		fBeginCharMap.put("class"    , "endclass"   );
		fBeginCharMap.put("generate" , "endgenerate");
		fBeginCharMap.put("package"  , "endpackage" );
		fBeginCharMap.put("case"     , "endcase"     );
		fBeginCharMap.put("clocking" , "endclocking" );
		fBeginCharMap.put("config"   , "endconfig"   );
		fBeginCharMap.put("group"    , "endgroup"    );
		fBeginCharMap.put("interface", "endinterface");
		fBeginCharMap.put("primitive", "endprimitive");
		fBeginCharMap.put("program"  , "endprogram"  );
		fBeginCharMap.put("property" , "endproperty" );
		fBeginCharMap.put("specify"  , "endspecify"  );
		fBeginCharMap.put("sequence" , "endsequence" );
		fBeginCharMap.put("table"    , "endtable"    );
		
		fEndCharMap = new HashMap<String, String>();
		fEndCharMap.put(")", "(");
		fEndCharMap.put("}", "{");
		fEndCharMap.put("]", "[");
		fEndCharMap.put("end", "begin");
		fEndCharMap.put("endmodule"     , "module"  );
		fEndCharMap.put("endfunction"   , "function");
		fEndCharMap.put("endtask"       , "task"    );
		fEndCharMap.put("endclass"      , "class"   );
		fEndCharMap.put("endgenerate"   , "generate");
		fEndCharMap.put("endpackage"    , "package" );
		fEndCharMap.put("endcase"       , "case"     );
		fEndCharMap.put("endclocking"   , "clocking" );
		fEndCharMap.put("endconfig"     , "config"   );
		fEndCharMap.put("endgroup"      , "group"    );
		fEndCharMap.put("endinterface"  , "interface");
		fEndCharMap.put("endprimitive"  , "primitive");
		fEndCharMap.put("endprogram"    , "program"  );
		fEndCharMap.put("endproperty"   , "property" );
		fEndCharMap.put("endspecify"    , "specify"  );
		fEndCharMap.put("endsequence"   , "sequence" );
		fEndCharMap.put("endtable"      , "table"    );
		
	}

	@Override
	public void run() {
		ISourceViewer sv = fEditor.sourceViewer();
		IDocument doc = sv.getDocument();
		ITextSelection tsel = (ITextSelection)fEditor.getSite().getSelectionProvider().getSelection();
		
		int offset = tsel.getOffset();
		int len    = tsel.getLength();
		// If we have text selected, and we last searched forward, move our cursor to the end of the selection
		if ((len != 0) && (fLastSearchForward == true))  {
			offset = offset+len;
		}
		// Check for end of file
		if (offset >= doc.getLength())  {
			offset = doc.getLength()-1;
		}
		
		String st = null, en=null;
		boolean begin = false;
		boolean valid = false;
		int start_pos = -1;
		int end_pos   = -1;
		
		try {
			int ch = doc.getChar(offset);
			int prevch = 0;
			if (offset > 0)  {
				prevch = doc.getChar(offset-1);
			}
			
			// If we have whitespace (or end of line) step back 1 character
			// This will allow us to jump between begin & end with out moving the cursor
			if ((ch == (int) ' ') || (ch == (int) '\t') || (ch == (int) '\r') || (ch == (int) '\n') || (ch == -1))  {
				offset --;
				ch = doc.getChar(offset);
				if (offset > 0)  {
					prevch = doc.getChar(offset-1);
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
				start_pos = offset+1;
				offset --;
			// Search for normal open brace ([{
			} else if (fBeginCharMap.containsKey(prev_st_c)) {
				begin = true;
				st = prev_st_c;
				en = fBeginCharMap.get(prev_st_c);
				valid = true;
				start_pos = offset-1;
				// Search for normal close brace (]}
			} else if (fEndCharMap.containsKey(prev_st_c)) {
				begin = false;
				st = prev_st_c;
				en = fEndCharMap.get(prev_st_c);
				valid = true;
				start_pos = offset;
				offset -= 2;
			// Failing these, start searching for begin/end which means we have to build up words
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
					String str = doc.get(st_off, (en_off-st_off+1));
				
					if (fBeginCharMap.containsKey(str)) {
						st = str;
						en = fBeginCharMap.get(str);
						offset=en_off+1;
						begin = true;
						valid = true;
						start_pos = offset;
					} else if (fEndCharMap.containsKey(str)) {
						st = str;
						en = fEndCharMap.get(str);
						offset=st_off-1;
						begin = false;
						valid = true;
						start_pos = offset;
					}
				}
			}

			if (valid) {
				SVDocumentTextScanner scanner = new SVDocumentTextScanner(doc, SVDocumentPartitions.SV_PARTITIONING, 
						new String[] {
						SVDocumentPartitions.SV_MULTILINE_COMMENT,
						SVDocumentPartitions.SV_SINGLELINE_COMMENT,
						SVDocumentPartitions.SV_STRING},
						"", offset, begin, true);

				int n_st=1, n_en=0;

				do {
					if ((ch = scanner.get_ch()) == -1) {
						break;
					}

					String t;
					if (ch == '\"') {
						t = scanner.readString(ch);
					} else if ((t = scanner.readIdentifier(ch)) == null) {
						scanner.get_ch();
						t = "" + (char)ch;
					}

					if (t.equals(st)) {
						n_st++;
					} else if (t.equals(en)) {
						n_en++;
					}
				} while (n_st != n_en);

				if (n_st == n_en) {
					int pos = (int)scanner.getPos();

					if (!begin) {
						pos++;
					}
					end_pos = pos;
					
					int length = 0;
					if ((start_pos != -1) && (end_pos != -1))  {
						length = end_pos-start_pos;
						sv.setSelectedRange(start_pos, length);
//						sv.setSelectedRange(pos, 0);
					}
					else  {
						sv.setSelectedRange(pos, 0);
					}

					sv.revealRange(pos, 0);
					fLastSearchForward = begin;
				}
			}
		} catch (BadLocationException e) { }
	}

}
