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
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.ui.texteditor.TextEditorAction;

import com.sun.xml.internal.ws.util.StringUtils;

public class AddNdocsAction extends TextEditorAction {
	private SVEditor fEditor;
	// These fields are used to help derive the direction to search in if we
	// have text selected (presumably from the
	// previous match that we are toggling between
	private LogHandle fLog;
	private int fStartline;
	private boolean fFullFile = false;
	private boolean fPrefShowModuleInterfacePorts = false;
	private ArrayList<Tuple<Object, String>> fComments = new ArrayList<Tuple<Object, String>>();

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
		boolean foundit = false;

		fStartline = tsel.getStartLine() + 1;

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
			fLog.debug("Start line: " + fStartline);

		} catch (Exception e) {
			e.printStackTrace();
		}

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
				String leadingWS = "";
				String current_line = text.getLine(highest_line-1);
				for (int i=0; i<current_line.length(); i++)  {
					char ch = current_line.charAt(i);
					if ((ch == ' ') || (ch == '\t'))  {
						leadingWS += ch;
					}
					// first non-whitespace character
					else  {
						break;
					}
				}
				highest_comment = leadingWS + highest_comment;		// Whitespace added at start of string
				highest_comment = highest_comment.replaceAll("\n", "\n" + leadingWS); // at each new line
				highest_comment = highest_comment.substring(0, highest_comment.length()-leadingWS.length());	// remove the last indent...
				
				doc.replace(doc.getLineOffset(highest_line - 1), 0, highest_comment);
				fComments.remove(highest_index);
				
				// Move the caret and reset the view
				if ((fStartline < doc.getNumberOfLines() + 1) && (fStartline > -1)) {
					int length_of_comment = highest_comment.length() - highest_comment.replace("\n", "").length();
					text.setCaretOffset(doc.getLineOffset(fStartline - 1+length_of_comment));
					fEditor.sourceViewer().revealRange(doc.getLineOffset(fStartline - 1+length_of_comment), 0);
				}

			}
		} catch (Exception e) {
			e.printStackTrace();
		}
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

		if (fFullFile || (fStartline == SVDBLocation.unpackLineno(child.getLocation()))) {
			switch (child.getType()) {
			case InterfaceDecl:
			case ModuleDecl:
				sb.append("/**\n");
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

				sb.append(" * " + typestring + ": " + ((SVDBModIfcDecl) child).getName() + "\n");
				sb.append(" * \n");
				sb.append(" * " + typestring + " description needed\n");
				sb.append(" * \n");
				if (fPrefShowModuleInterfacePorts && ((SVDBModIfcDecl) child).getPorts().size() > 0) {
					sb.append(" * Ports:\n");
					for (SVDBParamPortDecl pp : ((SVDBModIfcDecl) child).getPorts()) {
						sb.append(GetParamPortString(pp));
					}
				}
				sb.append(" */\n");
				comment = sb.toString();
				break;
			case ClassDecl:
				comment = "/**\n" + " * Class: " + ((SVDBClassDecl) child).getName() + "\n" + " *\n" + " * Class description needed\n" + " */\n";
				break;
			case PackageDecl:
				comment = "/**\n" + " * Package: " + ((SVDBPackageDecl) child).getName() + "\n" + " *\n" + " * Package description needed\n" + " */\n";
				break;
			case ProgramDecl:
				comment = "/**\n" + " * Program: " + ((SVDBProgramDecl) child).getName() + "\n" + " *\n" + " * Program description needed\n" + " */\n";
				break;
			case Function:
				sb.append("/**\n");
				sb.append(" * Function: " + ((SVDBFunction) child).getName() + "\n");
				sb.append(" * \n");
				sb.append(" * Function description needed\n");
				sb.append(" * \n");
				sb.append(" * Parameters:\n");
				for (SVDBParamPortDecl pp : ((SVDBFunction) child).getParams()) {
					sb.append(GetParamPortString(pp));
				}
				sb.append(" * \n");
				sb.append(" * Returns:\n");
				sb.append(" *   " + ((SVDBFunction) child).getReturnType().toString() + "\n");
				sb.append(" */\n");
				comment = sb.toString();
				break;
			case Task:
				sb.append("/**\n");
				sb.append(" * Task: " + ((SVDBTask) child).getName() + "\n");
				sb.append(" * \n");
				sb.append(" * Task description needed\n");
				sb.append(" * \n");
				sb.append(" * Parameters:\n");
				for (SVDBParamPortDecl pp : ((SVDBTask) child).getParams()) {
					sb.append(GetParamPortString(pp));
				}
				sb.append(" */\n");
				comment = sb.toString();
				break;
			default:
				break;
			}
		}
		
		if (fFullFile)  {
			// Full file... keep the comment null so that we keep going through
			// hierarchy
			fComments.add(new Tuple<Object, String>(SVDBLocation.unpackLineno(child.getLocation()), comment));
		}
		// Specific location ... 
		else if ((fStartline == SVDBLocation.unpackLineno(child.getLocation())))  {
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
	private String GetParamPortString(SVDBParamPortDecl pp) {
		String str;
		str = " * - ";
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
		str += "\n";
		return (str);
	}

	/**
	 * This function loops through all the children of parent checking to see if
	 * the children are on the appropriate line
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
//				foundit = CreateComment(child);
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
}
