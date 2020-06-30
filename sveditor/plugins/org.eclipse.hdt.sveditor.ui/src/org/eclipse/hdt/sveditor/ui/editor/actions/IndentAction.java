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


package org.eclipse.hdt.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.indent.ISVIndenter;
import org.eclipse.hdt.sveditor.core.indent.SVIndentScanner;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;

public class IndentAction extends TextEditorAction {
	
	public IndentAction(ResourceBundle bundle, String prefix, SVEditor editor) {
		super(bundle, prefix, editor);
		update();
	}
	
	
	
	@Override
	public boolean isEnabled() {
		return true;
		// return super.isEnabled();
	}



	@Override
	public void run() {
		ITextSelection 	sel = getSelection();
		ITextEditor te = getTextEditor();
		IDocument 		doc = getTextEditor().getDocumentProvider().getDocument(
				getTextEditor().getEditorInput());
		int start_line, end_line;
		int current_line;
		boolean full_file = false;
		
		// Don't yet try to indent entire files
		if (sel.getLength() == 0) {
			full_file = true;
		}

		try {
			if (full_file) {
				start_line   = doc.getLineOfOffset(0);
				end_line     = doc.getLineOfOffset(doc.getLength()-1);
				current_line = doc.getLineOfOffset(sel.getOffset());		// Current line we are on
			} else {
				start_line   = doc.getLineOfOffset(sel.getOffset());
				end_line     = doc.getLineOfOffset(sel.getOffset() + sel.getLength());
				current_line = end_line;									// Current line we are on
			}
			
			SVDocumentTextScanner text_scanner =  new SVDocumentTextScanner(doc, 0);
			
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			SVIndentScanner scanner = new SVIndentScanner(text_scanner);
			
			indenter.init(scanner);
			
			indenter.setIndentIncr(SVUiPlugin.getDefault().getIndentIncr());
			
			// Don't use adaptive indent if we're indenting the entire file
			if (!full_file) {
				indenter.setAdaptiveIndent(true);
				indenter.setAdaptiveIndentEnd(start_line-1);
			}
			
			String str = null;
			int length = 0;
			for (int i=start_line; i<end_line; i++) {
				length += doc.getLineLength(i);
			}
			
			try {
				str = indenter.indent(start_line+1, end_line);
				doc.replace(doc.getLineOffset(start_line), length, str); 
			} catch (Exception e) {
				e.printStackTrace();
			}
			// Set the cursor at the line our cursor is on (or end of selection if this applies)
			// Because we not doing anything to the line delimiters, we just need to make our way pass the appropriate number of 
			// line delimiters and set the cursor location at this point
			//
			// There doesn't seem to be a way to directly go to the line number that I can find, so I am getting the line delimiter 
			// N times, and then calculating the offset from that point in the scanner
			//
			// TODO: Matt, sorry about the TODO, but I have to believe there is a more elegant way of doing this, this is garbage code
			text_scanner.seek(0);					// Start of doc
			text_scanner.setSkipComments(false);	// Want to include comment lines here
			int ch = -1;
			// Loop till we get to the line the cursor was on at the start, current_line
			for (int i=0; i<current_line; i++)  {
				String line_delim = doc.getLineDelimiter(i);		// Find the current line delimiter
				
				// Scan across the line till we get to the end of the line
				// The mess below should really be replaced with a search (line_delim) but can't find that either
				int j = 0;	// index within line_delim
				while ((ch = text_scanner.get_ch()) >= 0)  {
					// Look for possibly 2 characters (\r\n)
					if (ch == (int) line_delim.charAt(j))  {
						j++;
						if (j >= line_delim.length())  {
							// Found them all... stop here!!! and move onto the next line
							break;
						}
					}
					// Not found, reset match index
					else  {
						j = 0;
					}
				}
			}
			
			// Found location, go ahead and set the cursor there, with nothing selected
			if (ch >= 0)  {
				te.selectAndReveal((int) text_scanner.getPos(), 0);
			}
			
			// System.out.println("Indent result=\n\"" + str + "\"");
			
		} catch (BadLocationException e) {
			
		}
	}

    private ITextSelection getSelection() {
        ISelectionProvider provider= getSelectionProvider();
        if (provider != null) {

                ISelection selection= provider.getSelection();
                if (selection instanceof ITextSelection)
                        return (ITextSelection) selection;
        }

        // null object
        return TextSelection.emptySelection();
        
    }
    
    private ISelectionProvider getSelectionProvider() {
        ITextEditor editor= getTextEditor();
        if (editor != null) {
                return editor.getSelectionProvider();
        }
        return null;
    }


	

}
