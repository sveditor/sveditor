package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCoverageCrossBinsSelectStmt extends SVDBStmt {
	private SVDBCoverageBinsType	fBinsType;
	private SVDBExpr				fBinsName;
	private SVDBExpr				fSelectCondition;
	private SVDBExpr				fIffExpr;
	
	public SVDBCoverageCrossBinsSelectStmt() {
		super(SVDBItemType.CoverageCrossBinsSelectStmt);
	}
	
	public SVDBCoverageBinsType getBinsType() {
		return fBinsType;
	}
	
	public void setBinsType(SVDBCoverageBinsType type) {
		fBinsType = type;
	}
	
	public void setBinsType(String type) {
		if (type.equals("ignore_bins")) {
			fBinsType = SVDBCoverageBinsType.IgnoreBins;
		} else if (type.equals("illegal_bins")) {
			fBinsType = SVDBCoverageBinsType.IllegalBins;
		} else {
 			fBinsType = SVDBCoverageBinsType.Bins; 
		}
	}
	
	public SVDBExpr getBinsName() {
		return fBinsName;
	}
	
	public void setBinsName(SVDBExpr name) {
		fBinsName = name;
	}
	
	public SVDBExpr getSelectCondition() {
		return fSelectCondition;
	}
	
	public void setSelectCondition(SVDBExpr expr) {
		fSelectCondition = expr;
	}
	
	public SVDBExpr getIffExpr() {
		return fIffExpr;
	}
	
	public void setIffExpr(SVDBExpr iff) {
		fIffExpr = iff;
	}

}
