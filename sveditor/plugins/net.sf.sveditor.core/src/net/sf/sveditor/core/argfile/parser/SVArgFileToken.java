package net.sf.sveditor.core.argfile.parser;

import net.sf.sveditor.core.db.SVDBLocation;

public class SVArgFileToken {
	protected String					fImage;
	protected boolean					fIsPath;
	protected boolean					fIsOption;
	protected String					fOptionVal;
	protected String					fOptionOp;
	protected long						fStartLocation;
	
	public String getImage() {
		return fImage;
	}

	public boolean isPath() {
		return fIsPath;
	}
	
	public boolean isOption() {
		return fIsOption;
	}
	
	public String getOptionVal() {
		return fOptionVal;
	}
	
	public void setOptionVal(String val) {
		fOptionVal = val;
	}
	
	public String getOptionOp() {
		return fOptionOp;
	}
	
	public void setOptionOp(String op) {
		fOptionOp = op;
	}
	
	public long getStartLocation() {
		return fStartLocation;
	}
	
	public SVArgFileToken duplicate() {
		SVArgFileToken ret = new SVArgFileToken();
		ret.fImage = fImage;
		ret.fIsPath = fIsPath;
		ret.fIsOption = fIsOption;
		ret.fStartLocation = fStartLocation;
		ret.fOptionVal = fOptionVal;
		ret.fOptionOp = fOptionOp;
	
		return ret;
	}
}
