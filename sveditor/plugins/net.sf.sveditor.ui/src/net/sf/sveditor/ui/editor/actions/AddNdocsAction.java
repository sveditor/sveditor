/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Steven Dawson - initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.editor.actions;

import java.util.ArrayList;
import java.util.ResourceBundle;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBProgramDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.docs.DocCommentAdder;
import net.sf.sveditor.core.docs.IDocCommentAdder;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;
// TODO: Break this out into a separate class, that can be called from this action (and others)
// TODO: Check for comments above this:
//       - If they are NDOC compliant ... skip
//       - If not, assume that the comment is the "description field" and insert it there

public class AddNdocsAction extends TextEditorAction {
	private SVEditor fEditor;
	// These fields are used to help derive the direction to search in if we
	// have text selected (presumably from the
	// previous match that we are toggling between
	private LogHandle fLog;
	private int fCurrentLine;
	private boolean fFullFile = false;
	private ArrayList<Tuple<Object, String>> fComments = new ArrayList<Tuple<Object, String>>();
	String fLineDelimiter = "\n";

	/**
	 * @param bundle
	 * @param prefix
	 * @param editor
	 * @param fullfile
	 *            - parse full file if true
	 */
	public AddNdocsAction(ResourceBundle bundle, String prefix, SVEditor editor, boolean fullfile) {
		super(bundle, prefix, editor);
		fEditor = editor;
		fLog = LogFactory.getLogHandle("SVEAddNdocs");
		fFullFile = fullfile;
		fLineDelimiter = TextUtilities.getDefaultLineDelimiter(editor.getDocument());
	}

	/**
	 * Rules:
	 */
	@Override
	public void run() {
		ISourceViewer sv = fEditor.sourceViewer();
		IDocument doc = sv.getDocument();
		StyledText text = fEditor.sourceViewer().getTextWidget();
		ITextSelection tsel = (ITextSelection) fEditor.getSite().getSelectionProvider().getSelection();
		SVDBFile svdbf = fEditor.getSVDBFile();
		int start_offset = tsel.getOffset();

		fCurrentLine = tsel.getStartLine() + 1;
		// Now insert the comment if it exists
		try {
			SVDocumentTextScanner text_scanner = new SVDocumentTextScanner(doc, 0);
			IDocCommentAdder docadder = new DocCommentAdder(svdbf, null, text_scanner, fFullFile);
			docadder.SetLineDelimiter(doc.getLineDelimiter(0));
			fComments = docadder.AddComments(fCurrentLine);

			// Move the caret and reset the view
			if (fComments.size() > 0) {
				String comment = fComments.get(0).second();
				int comment_length = comment.length();
				Integer offset = (Integer)fComments.get(0).first();
				doc.replace(doc.getLineOffset(offset - 1), 0, comment);

				if ((fCurrentLine < doc.getNumberOfLines() + 1) && (fCurrentLine > -1)) {
					text.setCaretOffset(start_offset + comment_length);
					fEditor.sourceViewer().revealRange(start_offset + comment_length, 0);
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
