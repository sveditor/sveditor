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

package net.sf.sveditor.core.docs;

import java.util.ArrayList;

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
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.ITextScanner;

// TODO: Check for comments above this:
//       - If they are NDOC compliant ... skip
//       - If not, assume that the comment is the "description field" and insert it there

/**
 * Adds NDOCS to a given file if "fullFile" is true, else adds a NDOC compliant comment above the current line
 * 
 * @author sdawson
 *
 */
public class DocCommentAdder implements IDocCommentAdder {
	private ITextScanner fScanner;
	private LogHandle fLog;
	private int fCurrentLine;
	private boolean fFullFile = false;
	private boolean fPrefShowModuleInterfacePorts = false;
	private ArrayList<Tuple<Object, String>> fComments = new ArrayList<Tuple<Object, String>>();
	private SVDBFile fSVDBFile;
	String fLineDelimiter = "\n";
	private String[] fLines;

	/**
	 * @param svdbfile
	 *            - svdb file that we are going to be parsing for port information
	 * @param scanner
	 * @param fullfile
	 *            - parse full file if true
	 */
	public DocCommentAdder(SVDBFile svdbfile, ITextScanner scanner, boolean fullfile) {
		fScanner = scanner;
		fFullFile = fullfile;
		fLog = LogFactory.getLogHandle("SVEDocCommentAdder");
		fSVDBFile = svdbfile;
	}

	/**
	 * Sets the line delimiter to be used.... defaults to \n
	 * 
	 * @param linedelimiter
	 */
	public void SetLineDelimiter(String linedelimiter) {
		fLineDelimiter = linedelimiter;
	}

	/**
	 * Rules:
	 * 
	 * @return An array list comprised of "Line number" and comments to be added
	 */
	@Override
	public ArrayList<Tuple<Object, String>> addcomments(int currentline) {
		fCurrentLine = currentline;

		// Convert the text into a string array which might be useful to us
		// TODO: there must be a better way of doing this... this is painful
		int ch = 0;
		String thefile = "";
		// Read in teh file
		while (ch != -1) {
			ch = fScanner.get_ch();
			thefile += (char) ch;
		}
		thefile = thefile.substring(0, thefile.length() - 2); // Remove the -1 at the end of the file

		fLines = thefile.split(fLineDelimiter);

		// Now insert the comment if it exists
		try {
			ComputeComments();
			return (fComments);
		} catch (Exception e) {
			e.printStackTrace();
		}
		return (null);
	}

	private boolean ComputeComments() {
		boolean foundit = false;
		try {
			Iterable<ISVDBChildItem> children = fSVDBFile.getChildren();
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
			// Figure out what the leading whitespace is on the current line
			String current_line = fLines[SVDBLocation.unpackLineno(child.getLocation()) - 1];

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
				comment = leadingWS + "/**" + fLineDelimiter + leadingWS + " * Class: " + ((SVDBClassDecl) child).getName() + fLineDelimiter + leadingWS + " *" + fLineDelimiter + leadingWS + " * Class description needed" + fLineDelimiter + leadingWS + " */" + fLineDelimiter;
				break;
			case PackageDecl:
				comment = leadingWS + "/**" + fLineDelimiter + leadingWS + " * Package: " + ((SVDBPackageDecl) child).getName() + fLineDelimiter + leadingWS + " *" + fLineDelimiter + leadingWS + " * Package description needed" + fLineDelimiter + leadingWS + " */" + fLineDelimiter;
				break;
			case ProgramDecl:
				comment = leadingWS + "/**" + fLineDelimiter + leadingWS + " * Program: " + ((SVDBProgramDecl) child).getName() + fLineDelimiter + leadingWS + " *" + fLineDelimiter + leadingWS + " * Program description needed" + fLineDelimiter + leadingWS + " */" + fLineDelimiter;
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
				if (((SVDBFunction) child).getReturnType() != null)  {
					sb.append(leadingWS + " *   " + ((SVDBFunction) child).getReturnType().toString() + fLineDelimiter);
				}
				else  {
					sb.append(leadingWS + " *   " + "void" + fLineDelimiter);
				}
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
					foundit = CheckChildren((ISVDBScopeItem) child);
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
