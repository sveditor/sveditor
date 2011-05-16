package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBCrossBinsSelectConditionExpr extends SVDBExpr {
	private SVDBExpr				fBinsExpr;
	private List<SVDBExpr>			fIntersectList;
	
	public SVDBCrossBinsSelectConditionExpr() {
		super(SVDBItemType.CrossBinsSelectConditionExpr);
		fIntersectList = new ArrayList<SVDBExpr>();
	}
	
	public void setBinsExpr(SVDBExpr expr) {
		fBinsExpr = expr;
	}
	
	public SVDBExpr getBinsExpr() {
		return fBinsExpr;
	}
	
	public List<SVDBExpr> getIntersectList() {
		return fIntersectList;
	}

}
