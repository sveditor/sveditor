package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBSequenceMatchItemExpr extends SVDBExpr {
	private SVDBExpr			fExpr;
	private List<SVDBExpr>		fMatchItemList;
	private SVDBExpr			fSequenceAbbrev;
	
	public SVDBSequenceMatchItemExpr() {
		super(SVDBItemType.SequenceMatchItemExpr);
		fMatchItemList = new ArrayList<SVDBExpr>();
	}

	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void addMatchItemExpr(SVDBExpr expr) {
		fMatchItemList.add(expr);
	}
	
	public List<SVDBExpr> getMatchItemExprList() {
		return fMatchItemList;
	}
	
	public void setSequenceAbbrev(SVDBExpr expr) {
		fSequenceAbbrev = expr;
	}
	
	public SVDBExpr getSequenceAbbrev() {
		return fSequenceAbbrev;
	}
}
