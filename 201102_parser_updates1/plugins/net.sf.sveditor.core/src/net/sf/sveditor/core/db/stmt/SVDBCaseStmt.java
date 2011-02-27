package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBCaseStmt extends SVDBStmt {
	private SVExpr						fExpr;
	private List<SVDBCaseItem>			fCaseItemList;
	
	public SVDBCaseStmt() {
		super(SVDBItemType.CaseStmt);
		fCaseItemList = new ArrayList<SVDBCaseItem>();
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public List<SVDBCaseItem> getCaseItemList() {
		return fCaseItemList;
	}
	
	public void addCaseItem(SVDBCaseItem item) {
		fCaseItemList.add(item);
	}

}
