package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBSequenceRepetitionExpr extends SVDBExpr {
	private String				fRepType;
	private SVDBExpr			fExpr;
	
	public SVDBSequenceRepetitionExpr() {
		super(SVDBItemType.SequenceRepetitionExpr);
	}
	
	public void setRepType(String t) {
		fRepType = t;
	}
	
	public String getRepType() {
		return fRepType;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
