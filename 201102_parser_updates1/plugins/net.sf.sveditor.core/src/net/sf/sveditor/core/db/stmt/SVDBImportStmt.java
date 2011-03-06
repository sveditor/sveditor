package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVStringExpr;

public class SVDBImportStmt extends SVDBStmt {
	
	private List<SVStringExpr>			fImportList;
	
	public SVDBImportStmt() {
		super(SVDBItemType.ImportStmt);
		fImportList = new ArrayList<SVStringExpr>();
	}
	
	public List<SVStringExpr> getImportList() {
		return fImportList;
	}
	
	public void addImport(SVStringExpr imp) {
		fImportList.add(imp);
	}

}
