package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBStringExpr;

public class SVDBImportStmt extends SVDBStmt {
	
	private List<SVDBStringExpr>			fImportList;
	
	public SVDBImportStmt() {
		super(SVDBItemType.ImportStmt);
		fImportList = new ArrayList<SVDBStringExpr>();
	}
	
	public List<SVDBStringExpr> getImportList() {
		return fImportList;
	}
	
	public void addImport(SVDBStringExpr imp) {
		fImportList.add(imp);
	}

}
