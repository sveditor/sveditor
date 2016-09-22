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

import java.util.ResourceBundle;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBGenerateIf;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;

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
	 * Parses the children of the class... filtering out what we want to stop on
	 * 
	 * @param parent
	 */
	private void ProcessModuleDecl(SVDBModIfcDecl parent) {
		for (ISVDBChildItem child : parent.getChildren()) {
			fLog.debug("ProcessModuleDecl: line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
			CheckChild(child);
		}
	}

	/**
	 * Parses the children of the class... filtering out what we want to stop on
	 * 
	 * @param parent
	 */
	private void ProcessClassDecl(SVDBClassDecl parent) {
		for (ISVDBChildItem child : parent.getChildren()) {
			fLog.debug("ProcessClassDecl: line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
			CheckChild(child);
		}
	}

	/**
	 * Parses the children of the generate... filtering out what we want to stop
	 * on
	 * 
	 * @param parent
	 */
	private void ProcessGenerate(SVDBGenerateBlock parent) {
		for (ISVDBChildItem child : parent.getChildren()) {
			fLog.debug("ProcessGenerate: line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
			CheckChild(child);
		}
	}

	/**
	 * Parses the children of the generate... filtering out what we want to stop
	 * on
	 * 
	 * @param parent
	 */
	private void ProcessGenerateIf(SVDBGenerateIf parent) {
		for (ISVDBChildItem child : parent.getChildren()) {
			fLog.debug("ProcessGenerate: line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
			CheckChild(child);
		}
	}

	private void CheckChild(ISVDBChildItem child) {
		fLog.debug("line [" + SVDBLocation.unpackLineno(child.getLocation()) + "] contains type " + child.getType().toString());
		switch (child.getType()) {
		case ModuleDecl:
			CompareLocation(child);
			ProcessModuleDecl((SVDBModIfcDecl) child);
			break;
		case ClassDecl:
			CompareLocation(child);
			ProcessClassDecl((SVDBClassDecl) child);
			break;
		case GenerateIf:
			CompareLocation(child);
			ProcessGenerateIf((SVDBGenerateIf) child);
			break;
		case GenerateBlock:
			CompareLocation(child);
			ProcessGenerate((SVDBGenerateBlock) child);
			break;
		// TODO SGD - Have this follow the outline preferences
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
		case PackageDecl:
		case ProgramDecl:
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
