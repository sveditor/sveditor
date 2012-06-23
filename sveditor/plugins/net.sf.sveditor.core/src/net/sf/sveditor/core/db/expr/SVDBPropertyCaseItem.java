package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.stmt.SVDBBodyStmt;

public class SVDBPropertyCaseItem extends SVDBBodyStmt {
	public List<SVDBExpr>				fExprList;
	public SVDBExpr						fStmt;
	
	public SVDBPropertyCaseItem() {
		super(SVDBItemType.PropertyCaseItem);
		fExprList = new ArrayList<SVDBExpr>();
	}
	
	public void addExpr(SVDBExpr expr) {
		fExprList.add(expr);
	}
	
	public void setStmt(SVDBExpr stmt) {
		fStmt = stmt;
	}
	
	public SVDBExpr getStmt() {
		return fStmt;
	}
	
}
