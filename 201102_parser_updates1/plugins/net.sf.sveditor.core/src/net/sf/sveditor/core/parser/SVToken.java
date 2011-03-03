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


package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBLocation;

public class SVToken {

	protected String						fImage;
	protected boolean						fIsString;
	protected boolean						fIsOperator;
	protected boolean						fIsNumber;
	protected boolean						fIsTime;
	protected boolean						fIsIdentifier;
	protected boolean						fIsKeyword;
	protected SVDBLocation					fStartLocation;

	public SVToken duplicate() {
		SVToken ret = new SVToken();
		ret.fImage         = fImage;
		ret.fIsString      = fIsString;
		ret.fIsOperator    = fIsOperator;
		ret.fIsNumber      = fIsNumber;
		ret.fIsTime        = fIsTime;
		ret.fIsIdentifier  = fIsIdentifier;
		ret.fIsKeyword     = fIsKeyword;
		ret.fStartLocation = fStartLocation.duplicate();
		
		return ret;
	}
	
	public boolean isIdentifier() {
		return fIsIdentifier;
	}
	
	public boolean isNumber() {
		return fIsNumber;
	}
	
	public boolean isOperator() {
		return fIsOperator;
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
	
	public boolean isKeyword() {
		return fIsKeyword;
	}
	
	public String getImage() {
		return fImage;
	}
	
	public SVDBLocation getStartLocation() {
		return fStartLocation;
	}
	
}
