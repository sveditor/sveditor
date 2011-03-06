package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVStringExpr;

public class SVDBExportStmt extends SVDBStmt {
	private List<SVStringExpr>			fExportList;
	
	public SVDBExportStmt() {
		super(SVDBItemType.ExportStmt);
		fExportList = new ArrayList<SVStringExpr>();
	}
	
	public List<SVStringExpr> getExportList() {
		return fExportList;
	}
	
	public void addExport(SVStringExpr exp) {
		fExportList.add(exp);
	}

}
