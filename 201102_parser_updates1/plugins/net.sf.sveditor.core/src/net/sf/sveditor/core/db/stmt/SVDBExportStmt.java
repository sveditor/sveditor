package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBStringExpr;

public class SVDBExportStmt extends SVDBStmt {
	private List<SVDBStringExpr>			fExportList;
	
	public SVDBExportStmt() {
		super(SVDBItemType.ExportStmt);
		fExportList = new ArrayList<SVDBStringExpr>();
	}
	
	public List<SVDBStringExpr> getExportList() {
		return fExportList;
	}
	
	public void addExport(SVDBStringExpr exp) {
		fExportList.add(exp);
	}

}
