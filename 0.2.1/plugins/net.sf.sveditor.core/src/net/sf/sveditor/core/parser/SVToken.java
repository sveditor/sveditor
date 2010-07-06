package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBLocation;

public class SVToken {

	protected String						fImage;
	protected boolean						fIsString;
	protected boolean						fIsOperator;
	protected boolean						fIsNumber;
	protected boolean						fIsIdentifier;
	protected boolean						fIsKeyword;
	protected SVDBLocation					fStartLocation;

	public SVToken duplicate() {
		SVToken ret = new SVToken();
		ret.fImage         = fImage;
		ret.fIsString      = fIsString;
		ret.fIsOperator    = fIsOperator;
		ret.fIsNumber      = fIsNumber;
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
