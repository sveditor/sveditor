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


package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

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
		IDocument 		doc = getTextEditor().getDocumentProvider().getDocument(
				getTextEditor().getEditorInput());
		int start_line, end_line;
		boolean full_file = false;
		
		// Don't yet try to indent entire files
		if (sel.getLength() == 0) {
			full_file = true;
		}

		try {
			if (full_file) {
				start_line = doc.getLineOfOffset(0);
				end_line = doc.getLineOfOffset(doc.getLength()-1);
			} else {
				start_line = doc.getLineOfOffset(sel.getOffset());
				end_line = doc.getLineOfOffset(sel.getOffset() + sel.getLength());
			}
			
			SVDocumentTextScanner text_scanner =  new SVDocumentTextScanner(doc, 0);
			
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			SVIndentScanner scanner = new SVIndentScanner(text_scanner);
			
			indenter.init(scanner);
			
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
