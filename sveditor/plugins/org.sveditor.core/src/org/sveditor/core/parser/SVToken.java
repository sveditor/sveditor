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


package org.sveditor.core.parser;


public class SVToken implements ISVKeywords, ISVOperators {

	protected String						fImage;
	protected boolean						fIsString;
	protected OP							fOperator;
	protected boolean						fIsNumber;
	protected boolean						fIsTime;
	protected boolean						fIsIdentifier;
//	protected boolean						fIsKeyword;
	protected KW							fKeyword;
	protected boolean						fIsPath;
//	protected SVDBLocation					fStartLocation;
	protected long							fStartLocation;

	public SVToken duplicate() {
		SVToken ret = new SVToken();
		ret.fImage         = fImage;
		ret.fIsString      = fIsString;
		ret.fOperator      = fOperator;
		ret.fIsNumber      = fIsNumber;
		ret.fIsTime        = fIsTime;
		ret.fIsIdentifier  = fIsIdentifier;
		ret.fKeyword       = fKeyword;
		ret.fIsPath        = fIsPath;
//		ret.fStartLocation = fStartLocation.duplicate();
		ret.fStartLocation = fStartLocation;
		
		return ret;
	}
	
	public boolean isIdentifier() {
		return fIsIdentifier;
	}
	
	public boolean isNumber() {
		return fIsNumber;
	}
	
	public boolean isOperator() {
		return (fOperator != null);
	}
	
	public boolean isOperator(String ... ops) {
		if (fOperator != null) {
			for (String op : ops) {
				if (fOperator.getImg().equals(op)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public boolean isPath() {
		return fIsPath;
	}
	
	/**
	 * Return is true when the number is
	 * a time constant
	 * 
	 * @return
	 */
	public boolean isTime() {
		return fIsTime;
	}
	
	public boolean isString() {
		return fIsString;
	}
	
	public boolean isKeyword() {
		return (fKeyword != null);
	}
	
	public boolean isOp(OP op) {
		return (fOperator == op);
	}
	
	public boolean isKW(KW kw) {
		return (fKeyword == kw);
	}
	
	public String getImage() {
		if (fKeyword != null) {
			return fKeyword.getImg();
		} else if (fOperator != null) {
			return fOperator.getImg();
		} else {
			return fImage;
		}
	}
	
	public long getStartLocation() {
		return fStartLocation;
	}
	
}
