package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFirstMatchExpr extends SVDBExpr {
	private SVDBExpr				fExpr;
	private List<SVDBExpr>			fSequenceMatchItems;		

	public SVDBFirstMatchExpr() {
		super(SVDBItemType.FirstMatchExpr);
		fSequenceMatchItems = new ArrayList<SVDBExpr>();
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void addSequenceMatchItem(SVDBExpr expr) {
		fSequenceMatchItems.add(expr);
	}
	
	public List<SVDBExpr> getSequenceMatchItems() {
		return fSequenceMatchItems;
	}
	
}
