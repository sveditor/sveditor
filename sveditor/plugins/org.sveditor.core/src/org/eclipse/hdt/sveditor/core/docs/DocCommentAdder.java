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

package org.sveditor.core.docs;

import java.util.ArrayList;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.ISVDBScopeItem;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBDocComment;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBFunction;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.SVDBModIfcDecl;
import org.sveditor.core.db.SVDBPackageDecl;
import org.sveditor.core.db.SVDBProgramDecl;
import org.sveditor.core.db.SVDBTask;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.search.SVDBFindDocComment;
import org.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.sveditor.core.log.ILogLevel;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.scanutils.ITextScanner;

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
	private LogHandle fLog;
	private int fCurrentLine;
	private boolean fFullFile = false;
	private boolean fPrefShowModuleInterfacePorts = false;
	private ArrayList<Tuple<Object, String>> fComments = new ArrayList<Tuple<Object, String>>();
	private SVDBFile fSVDBFile;
	String fLineDelimiter = "\n";
	private ISVDBIndexIterator fIndexIterator;

	/**
	 * @param svdbfile
	 *            - svdb file that we are going to be parsing for port information
	 * @param fullfile
	 *            - parse full file if true
	 */
	public DocCommentAdder(SVDBFile svdbfile, ISVDBIndexIterator iterator, boolean fullfile) {
		fFullFile = fullfile;
		fLog = LogFactory.getLogHandle("SVEDocCommentAdder");
		fSVDBFile = svdbfile;
		fIndexIterator = iterator;
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
	public ArrayList<Tuple<Object, String>> AddComments(int currentline) {
		fCurrentLine = currentline;

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

		// Check if we already have a NDOC comment
		if (fIndexIterator != null)  {
			SVDBFindDocComment finder = new SVDBFindDocComment(fIndexIterator);
			SVDBDocComment docCom = finder.find(new NullProgressMonitor(), child);
	
			if(docCom != null) {
				fLog.debug(ILogLevel.LEVEL_MID,
					String.format("Did not find doc comment for(%s)", SVDBItem.getName(child)));
				return false;
			}
		}
		
		if (fFullFile || (fCurrentLine == SVDBLocation.unpackLineno(child.getLocation()))) {
			switch (child.getType()) {
			case InterfaceDecl:
			case ModuleDecl:
				sb.append("/**" + fLineDelimiter);
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

				sb.append(" * " + typestring + ": " + ((SVDBModIfcDecl) child).getName() + fLineDelimiter);
				sb.append(" * " + fLineDelimiter);
				sb.append(" * " + typestring + " description needed" + fLineDelimiter);
				sb.append(" * " + fLineDelimiter);
				if (fPrefShowModuleInterfacePorts && ((SVDBModIfcDecl) child).getPorts().size() > 0) {
					sb.append(" * Ports:" + fLineDelimiter);
					for (SVDBParamPortDecl pp : ((SVDBModIfcDecl) child).getPorts()) {
						sb.append(GetParamPortString(pp));
					}
				}
				sb.append(" */" + fLineDelimiter);
				comment = sb.toString();
				break;
			case ClassDecl:
				comment = "/**" + fLineDelimiter + " * Class: " + ((SVDBClassDecl) child).getName() + fLineDelimiter + " *" + fLineDelimiter + " * Class description needed" + fLineDelimiter + " */" + fLineDelimiter;
				break;
			case PackageDecl:
				comment = "/**" + fLineDelimiter + " * Package: " + ((SVDBPackageDecl) child).getName() + fLineDelimiter + " *" + fLineDelimiter + " * Package description needed" + fLineDelimiter + " */" + fLineDelimiter;
				break;
			case ProgramDecl:
				comment = "/**" + fLineDelimiter + " * Program: " + ((SVDBProgramDecl) child).getName() + fLineDelimiter + " *" + fLineDelimiter + " * Program description needed" + fLineDelimiter + " */" + fLineDelimiter;
				break;
			case Function:
				sb.append("/**" + fLineDelimiter);
				sb.append(" * Function: " + ((SVDBFunction) child).getName() + fLineDelimiter);
				sb.append(" * " + fLineDelimiter);
				sb.append(" * Function description needed" + fLineDelimiter);
				sb.append(" * " + fLineDelimiter);
				sb.append(" * Parameters:" + fLineDelimiter);
				for (SVDBParamPortDecl pp : ((SVDBFunction) child).getParams()) {
					sb.append(GetParamPortString(pp));
				}
				sb.append(" * " + fLineDelimiter);
				sb.append(" * Returns:" + fLineDelimiter);
				if (((SVDBFunction) child).getReturnType() != null)  {
					sb.append(" *   " + ((SVDBFunction) child).getReturnType().toString() + fLineDelimiter);
				}
				else  {
					sb.append(" *   " + "void" + fLineDelimiter);
				}
				sb.append(" */" + fLineDelimiter);
				comment = sb.toString();
				break;
			case Task:
				sb.append("/**" + fLineDelimiter);
				sb.append(" * Task: " + ((SVDBTask) child).getName() + fLineDelimiter);
				sb.append(" * " + fLineDelimiter);
				sb.append(" * Task description needed" + fLineDelimiter);
				sb.append(" * " + fLineDelimiter);
				sb.append(" * Parameters:" + fLineDelimiter);
				for (SVDBParamPortDecl pp : ((SVDBTask) child).getParams()) {
					sb.append(GetParamPortString(pp));
				}
				sb.append(" */" + fLineDelimiter);
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
	
	/**
	 * Returns the natural doc comment for the line specified
	 * @param line
	 * @return
	 */
	public String GetNDocAtLine (int line)  {
		String s = "";
		ArrayList<Tuple<Object, String>> al = AddComments(line);
		if (al.size() > 0)  {
			return (al.get(0).second());
		}

		return(s);
		
	}

}
