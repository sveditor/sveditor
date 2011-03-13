package net.sf.sveditor.core.db.stmt;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBAssertStmt extends SVDBStmt implements ISVDBNamedItem {
	private String					fName;
	private SVDBExpr					fExpr;
	private SVDBActionBlockStmt		fActionBlock;
	
	public SVDBAssertStmt() {
		this(SVDBItemType.AssertStmt);
	}
	
	protected SVDBAssertStmt(SVDBItemType type) {
		super(type);
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public void setActionBlock(SVDBActionBlockStmt stmt) {
		fActionBlock = stmt;
	}
	
	public SVDBActionBlockStmt getActionBlock() {
		return fActionBlock;
	}

}
