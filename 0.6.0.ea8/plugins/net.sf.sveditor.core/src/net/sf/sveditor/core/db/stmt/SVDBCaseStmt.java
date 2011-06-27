package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBCaseStmt extends SVDBStmt {
	
	public enum CaseType {
		Case,
		Casex,
		Casez,
		Randcase
	};
	
	private CaseType					fCaseType;
	private SVDBExpr						fExpr;
	private List<SVDBCaseItem>			fCaseItemList;
	
	public SVDBCaseStmt() {
		this(CaseType.Case);
	}
	
	public SVDBCaseStmt(CaseType type) {
		super(SVDBItemType.CaseStmt);
		fCaseItemList = new ArrayList<SVDBCaseItem>();
		fCaseType = type;
	}
	
	public CaseType getCaseType() {
		return fCaseType;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public List<SVDBCaseItem> getCaseItemList() {
		return fCaseItemList;
	}
	
	public void addCaseItem(SVDBCaseItem item) {
		fCaseItemList.add(item);
	}

}
