package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVExpr;

public class SVDBAssertStmt extends SVDBStmt implements ISVDBNamedItem {
	private String					fName;
	private SVExpr					fExpr;
	private SVDBActionBlockStmt		fActionBlock;
	
	public SVDBAssertStmt() {
		super(SVDBItemType.AssertStmt);
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setExpr(SVExpr expr) {
		fExpr = expr;
	}
	
	public SVExpr getExpr() {
		return fExpr;
	}
	
	public void setActionBlock(SVDBActionBlockStmt stmt) {
		fActionBlock = stmt;
	}
	
	public SVDBActionBlockStmt getActionBlock() {
		return fActionBlock;
	}

}
