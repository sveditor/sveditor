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


package org.eclipse.hdt.sveditor.core.indent;

public class SVIndentToken {
	protected SVIndentTokenType						fType;
	protected String								fLeadingWS;
	protected String								fTrailingWS = "";
	protected String								fImage;
	protected boolean								fEndLine;
	protected boolean								fStartLine;
	protected boolean								fDoIt;
	protected int									fPos;
	protected int									fLineno;
	
	public SVIndentToken(SVIndentTokenType type, String leading_ws, String image) {
		fType 		= type;
		fLeadingWS	= leading_ws;
		fTrailingWS = "";
		fImage 		= image;
		fDoIt		= true;
	}
	
	protected SVIndentToken(SVIndentTokenType type, String leading_ws) {
		fType 		= type; 
		fLeadingWS 	= leading_ws;
		fTrailingWS = "";
		fImage		= "";
		fDoIt		= true;
	}
	
	public boolean isId(String s) {
		return (getType() == SVIndentTokenType.Identifier &&
				getImage().equals(s));
	}
	
	public boolean isOp(String ... s) {
		if (getType() == SVIndentTokenType.Operator) {
			if (s.length == 0) {
				return true;
			} else {
				for (String s_i : s) {
					if (getImage().equals(s_i)) {
						return true;
					}
				}
			}
		}
		return false;
	}
	
	public boolean isPreProc() {
		return (getType() == SVIndentTokenType.Identifier &&
				getImage().startsWith("`"));
	}
	
	public void setPos(int pos) {
		fPos = pos;
	}
	
	public int getPos() {
		return fPos;
	}
	
	public void setLineno(int lineno) {
		fLineno = lineno;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public SVIndentTokenType getType() {
		return fType;
	}
	
	public void setTrailingWS(String trailing_ws) {
		fTrailingWS = trailing_ws;
	}
	
	public String getTrailingWS() {
		return fTrailingWS;
	}
	
	public boolean isEndLine() {
		return fEndLine;
	}
	
	public void setIsEndLine(boolean end) {
		fEndLine = end;
	}
	
	public boolean isStartLine() {
		return fStartLine;
	}
	
	public void setIsStartLine(boolean start) {
		fStartLine = start;
	}
	
	public String getLeadingWS() {
		return fLeadingWS;
	}
	
	public String getLeadingNonNewLineWS() {
		StringBuilder sb = new StringBuilder();
		for (int i=0; i<fLeadingWS.length(); i++) {
			if (fLeadingWS.charAt(i) != '\r' && 
					fLeadingWS.charAt(i) != '\n') {
				sb.append(fLeadingWS.charAt(i));
			}
		}
		
		return sb.toString();
	}
	
	public void setLeadingWS(String leading_ws) {
		fLeadingWS = leading_ws;
	}
	
	public String getImage() {
		return fImage;
	}
	
	public void setImage(String image) {
		fImage = image;
	}
	
	public boolean getDoIt() {
		return fDoIt;
	}
	
	public void setDoIt(boolean doit) {
		fDoIt = doit;
	}
	
	public boolean isBlankLine() {
		return (fStartLine && fEndLine && fImage.trim().equals(""));
	}
	
	public boolean isComment() {
		return (fType == SVIndentTokenType.SingleLineComment || fType == SVIndentTokenType.MultiLineComment);
	}

}
