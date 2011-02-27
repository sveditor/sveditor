package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBCaseItem extends SVDBBodyStmt {
	private List<SVExpr>		fCaseExprList;
	
	public SVDBCaseItem() {
		super(SVDBItemType.CaseItem);
		fCaseExprList = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getExprList() {
		return fCaseExprList;
	}
	
	public void addExpr(SVExpr expr) {
		fCaseExprList.add(expr);
	}
	

}
