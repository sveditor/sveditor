package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCaseItem extends SVDBBodyStmt {
	private List<SVDBExpr>		fCaseExprList;
	
	public SVDBCaseItem() {
		super(SVDBItemType.CaseItem);
		fCaseExprList = new ArrayList<SVDBExpr>();
	}
	
	public List<SVDBExpr> getExprList() {
		return fCaseExprList;
	}
	
	public void addExpr(SVDBExpr expr) {
		fCaseExprList.add(expr);
	}
	

}
