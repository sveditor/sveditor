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
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBProgramDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;

public class AddNdocsAction extends TextEditorAction {
	private SVEditor fEditor;
	// These fields are used to help derive the direction to search in if we
	// have text selected (presumably from the
	// previous match that we are toggling between
	private LogHandle fLog;
	private int fCurrentLine;
	private boolean fFullFile = false;
	private boolean fPrefShowModuleInterfacePorts = false;
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

		fCurrentLine = tsel.getStartLine() + 1;

		ComputeComments();

		// Now insert the comment if it exists
		try {
			while (fComments.size() != 0) {
				int highest_index = 0;
				int highest_line = 0;
				String highest_comment = "";
				for (int i = 0; i < fComments.size(); i++) {
					Tuple<Object, String> t = fComments.get(i);
					if ((int) t.first() > highest_line) {
						highest_comment = t.second();
						highest_index = i;
						highest_line = (int) t.first();
					}
					fLog.debug("Line[" + t.first() + "]");
				}
				int length_of_comment = highest_comment.length() - highest_comment.replace(fLineDelimiter, "").length();
				doc.replace(doc.getLineOffset(highest_line - 1), 0, highest_comment);
				fComments.remove(highest_index);

				// Move the caret and reset the view
				if ((fCurrentLine < doc.getNumberOfLines() + 1) && (fCurrentLine > -1)) {
					text.setCaretOffset(doc.getLineOffset(fCurrentLine - 1 + length_of_comment));
					fEditor.sourceViewer().revealRange(doc.getLineOffset(fCurrentLine - 1 + length_of_comment), 0);
				}

			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private boolean ComputeComments() {
		boolean foundit = false;
		try {
			Iterable<ISVDBChildItem> children = fEditor.getSVDBFile().getChildren();
			for (ISVDBChildItem child : children) {
				if (child instanceof ISVDBScopeItem) {
					fLog.debug("Found type " + child.getType().toString());
					foundit = CheckChildren((ISVDBScopeItem) child);
					if (!fFullFile && foundit) {
						// Found the comment, don't parse through rest of stuff
						// in file
						break;
					}
				}
			}
			fLog.debug("Start line: " + fCurrentLine);

		} catch (Exception e) {
			e.printStackTrace();
		}
		return (foundit);
	}

	/**
	 * Creates a comment before returning
	 * 
	 * @param child
	 * @return boolean - foundit - only used when not full file
	 */
	private boolean CreateComment(ISVDBChildItem child) {
		String comment = null;
		boolean foundit = false;
		StringBuilder sb = new StringBuilder();

		if (fFullFile || (fCurrentLine == SVDBLocation.unpackLineno(child.getLocation()))) {
			String leadingWS = "";
			String current_line = fEditor.sourceViewer().getTextWidget().getLine(SVDBLocation.unpackLineno(child.getLocation())-1);
			for (int i = 0; i < current_line.length(); i++) {
				char ch = current_line.charAt(i);
				if ((ch == ' ') || (ch == '\t')) {
					leadingWS += ch;
				}
				// first non-whitespace character
				else {
					break;
				}
			}

			switch (child.getType()) {
			case InterfaceDecl:
			case ModuleDecl:
				sb.append(leadingWS + "/**" + fLineDelimiter);
				String typestring = "undefined";
				switch (child.getType()) {
				case InterfaceDecl:
					typestring = "Interface";
					break;
				case ModuleDecl:
					typestring = "Module";
					break;
				default:
					break;
				}

				sb.append(leadingWS + " * " + typestring + ": " + ((SVDBModIfcDecl) child).getName() + fLineDelimiter);
				sb.append(leadingWS + " * " + fLineDelimiter);
				sb.append(leadingWS + " * " + typestring + " description needed" + fLineDelimiter);
				sb.append(leadingWS + " * " + fLineDelimiter);
				if (fPrefShowModuleInterfacePorts && ((SVDBModIfcDecl) child).getPorts().size() > 0) {
					sb.append(leadingWS + " * Ports:" + fLineDelimiter);
					for (SVDBParamPortDecl pp : ((SVDBModIfcDecl) child).getPorts()) {
						sb.append(GetParamPortString(pp, leadingWS));
					}
				}
				sb.append(leadingWS + " */" + fLineDelimiter);
				comment = sb.toString();
				break;
			case ClassDecl:
				comment = leadingWS + "/**" + fLineDelimiter + 
				leadingWS + " * Class: " + ((SVDBClassDecl) child).getName() + fLineDelimiter + 
				leadingWS + " *" + fLineDelimiter + 
				leadingWS + " * Class description needed" + fLineDelimiter + 
				leadingWS + " */" + fLineDelimiter;
				break;
			case PackageDecl:
				comment = leadingWS + "/**" + fLineDelimiter + 
				leadingWS + " * Package: " + ((SVDBPackageDecl) child).getName() + fLineDelimiter + 
				leadingWS + " *" + fLineDelimiter + 
				leadingWS + " * Package description needed" + fLineDelimiter + 
				leadingWS + " */" + fLineDelimiter;
				break;
			case ProgramDecl:
				comment = leadingWS + "/**" + fLineDelimiter + 
				leadingWS + " * Program: " + ((SVDBProgramDecl) child).getName() + fLineDelimiter + 
				leadingWS + " *" + fLineDelimiter + 
				leadingWS + " * Program description needed" + fLineDelimiter + 
				leadingWS + " */" + fLineDelimiter;
				break;
			case Function:
				sb.append(leadingWS + "/**" + fLineDelimiter);
				sb.append(leadingWS + " * Function: " + ((SVDBFunction) child).getName() + fLineDelimiter);
				sb.append(leadingWS + " * " + fLineDelimiter);
				sb.append(leadingWS + " * Function description needed" + fLineDelimiter);
				sb.append(leadingWS + " * " + fLineDelimiter);
				sb.append(leadingWS + " * Parameters:" + fLineDelimiter);
				for (SVDBParamPortDecl pp : ((SVDBFunction) child).getParams()) {
					sb.append(GetParamPortString(pp, leadingWS));
				}
				sb.append(leadingWS + " * " + fLineDelimiter);
				sb.append(leadingWS + " * Returns:" + fLineDelimiter);
				sb.append(leadingWS + " *   " + ((SVDBFunction) child).getReturnType().toString() + fLineDelimiter);
				sb.append(leadingWS + " */" + fLineDelimiter);
				comment = sb.toString();
				break;
			case Task:
				sb.append(leadingWS + "/**" + fLineDelimiter);
				sb.append(leadingWS + " * Task: " + ((SVDBTask) child).getName() + fLineDelimiter);
				sb.append(leadingWS + " * " + fLineDelimiter);
				sb.append(leadingWS + " * Task description needed" + fLineDelimiter);
				sb.append(leadingWS + " * " + fLineDelimiter);
				sb.append(leadingWS + " * Parameters:" + fLineDelimiter);
				for (SVDBParamPortDecl pp : ((SVDBTask) child).getParams()) {
					sb.append(GetParamPortString(pp, leadingWS));
				}
				sb.append(leadingWS + " */" + fLineDelimiter);
				comment = sb.toString();
				break;
			default:
				break;
			}
		}

		if (fFullFile) {
			// Full file... keep the comment null so that we keep going through
			// hierarchy
			fComments.add(new Tuple<Object, String>(SVDBLocation.unpackLineno(child.getLocation()), comment));
		}
		// Specific location ...
		else if ((fCurrentLine == SVDBLocation.unpackLineno(child.getLocation()))) {
			fComments.add(new Tuple<Object, String>(SVDBLocation.unpackLineno(child.getLocation()), comment));
			foundit = true;
		}
		return (foundit);
	}

	/**
	 * Returns a string "<direction> <type> <name>\n"
	 * 
	 * @param pp
	 * @return
	 */
	private String GetParamPortString(SVDBParamPortDecl pp, String leadingWS) {
		String str;
		str = leadingWS + " * - ";
		switch (pp.getDir()) {
		case 1:
			str += "input ";
			break;
		case 2:
			str += "output ";
			break;
		case 3:
			str += "inout ";
			break;
		default:
			break;
		}

		str += pp.getTypeName() + " ";
		for (SVDBVarDeclItem item : pp.fVarList) {
			str += item.getName() + " ";
		}
		str += fLineDelimiter;
		return (str);
	}

	/**
	 * This function loops through all the children of parent checking to see if the children are on the appropriate line
	 * 
	 * @param parent
	 */
	private boolean CheckChildren(ISVDBScopeItem parent) {
		boolean foundit = false;
		fLog.debug("line [" + SVDBLocation.unpackLineno(parent.getLocation()) + "] contains type " + parent.getType().toString());
		foundit = CreateComment(parent);
		// Not on this line ... keep digging
		for (ISVDBChildItem child : parent.getChildren()) {
			switch (child.getType()) {
			case InterfaceDecl:
			case ModuleDecl:
			case ClassDecl:
			case PackageDecl:
			case ProgramDecl:
				// Do we have a line match?
				// Not on current line, keep checking for children
				if (foundit == false) {
					foundit = CheckChildren((ISVDBScopeItem) child);
				}
				break;
			case Function:
			case Task:
				foundit = CreateComment(child);
				break;
			default:
				break;
			}
			// If we have a comment, our work here is done... return
			// immediately
			if (foundit) {
				return (foundit);
			}
		}
		return (foundit);
	}

	public String GetNDocAtLine(int line) {
		fCurrentLine = line;
		if (ComputeComments()) {
			return (fComments.get(0).second());
		} else {
			return ("");
		}
	}
}
