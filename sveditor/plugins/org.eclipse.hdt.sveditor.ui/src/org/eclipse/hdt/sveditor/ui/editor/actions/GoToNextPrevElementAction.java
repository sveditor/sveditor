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

import java.util.ResourceBundle;

import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBScopeItem;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;

import org.eclipse.hdt.sveditor.ui.editor.SVEditor;

public class GoToNextPrevElementAction extends TextEditorAction {
	private SVEditor fEditor;
	// These fields are used to help derive the direction to search in if we
	// have text selected (presumably from the
	// previous match that we are toggling between
	private LogHandle fLog;
	private boolean fDirection; // True - forward, False - backwards
	private int fStartline;
	private int fNewline;

	/**
	 * 
	 * @param bundle
	 * @param prefix
	 * @param editor
	 * @param direction
	 *            - Forward (true) or backwards (false)
	 */
	public GoToNextPrevElementAction(ResourceBundle bundle, String prefix, SVEditor editor, boolean direction) {
		super(bundle, prefix, editor);
		fEditor = editor;
		fDirection = direction;
		// fContentProvider = cp;
		fLog = LogFactory.getLogHandle("SVEGoToNextPrevElement");

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
		
		// TODO: This line added for #493 Editor: Find Next / Previous element doesn't behave when code folding is active 
		// The work-around is to expand everything at this point.
		// Ideally speaking the next line should be removed, and the "set_line" below should 
		// go to the "real line" not the visible line which is happening at the moment
		ProjectionAnnotationModel model = fEditor.getProjectionAnnotationModel();
		if (model != null)
			model.expandAll(0, doc.getNumberOfLines());
		
		fStartline = tsel.getStartLine() + 1;
		// Searching forward
		if (fDirection)
			fNewline = doc.getNumberOfLines() + 1;
		// Searching backwards
		else
			fNewline = -1;

		try {
			Iterable<ISVDBChildItem> children = fEditor.getSVDBFile().getChildren();
			for (ISVDBChildItem child : children) {
				fLog.debug("Found type " + child.getType().toString());
				CheckChild(child);
			}
			fLog.debug("Start line: " + fNewline);
			fLog.debug("New line: " + fNewline);

			// Move the caret and reset the view
			if ((fNewline < doc.getNumberOfLines() + 1) && (fNewline > -1)) {
				text.setCaretOffset(doc.getLineOffset(fNewline - 1));
				fEditor.sourceViewer().revealRange(doc.getLineOffset(fNewline - 1), 0);
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Parses the children of the element... filtering out what we want to stop on
	 * 
	 * @param parent
	 */
	private void ProcessParentItem(SVDBScopeItem parent) {
		for (ISVDBChildItem child : parent.getChildren()) {
			fLog.debug("ProcessParentItem: line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
			CheckChild(child);
		}
	}

	private void CheckChild(ISVDBChildItem child) {
		fLog.debug("line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
		switch (child.getType()) {
		// If the element has hierarchy... check it's children
		case ModuleDecl:
		case ClassDecl:
		case GenerateIf:
		case GenerateBlock:
		case PackageDecl:
		case ProgramDecl:
			CompareLocation(child);
			ProcessParentItem((SVDBScopeItem) child);
			break;
		// TODO SGD - Have this follow the outline preferences
		// if it doesn't have children, and is one of the following types... move to the location
		case ModIfcInst:
		case Function:
		case Task:
		case Bind:
		case ClockingBlock:
		case Constraint:
		case Covergroup:
		case Coverpoint:
		case Property:
		case AssertStmt:
		case ModportDecl:
		case Sequence:
		case TypedefStmt:
		case TypeExpr:
			CompareLocation(child);
			break;
		default:
			break;
		}
	}

	/**
	 * Compares the current location to our most recent location
	 * 
	 */
	private void CompareLocation(ISVDBChildItem child) {
		int childline = SVDBLocation.unpackLineno(child.getLocation());
		fLog.debug("Comparing: StartLine/Newline/Childline/Type " + fStartline + "/" + fNewline + "/" + childline + " - " + child.getType().toString());

		// if we have an uninitialized line number
		if (childline < 0) {
			return;
		}

		// Searching forward
		if (fDirection == true) {
			if ((childline > fStartline) && (childline < fNewline)) {
				fNewline = childline;
			}
		}
		// Searching backward
		else {
			if ((childline < fStartline) && (childline > fNewline)) {
				fNewline = childline;
			}
		}

	}
}
