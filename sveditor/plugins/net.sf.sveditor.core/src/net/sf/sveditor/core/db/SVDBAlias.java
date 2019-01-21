package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVDBAlias extends SVDBStmt {
	public SVDBExpr				fLvalue;
	public List<SVDBExpr>		fAliases;
	
	public SVDBAlias() {
		super(SVDBItemType.Alias);
		fAliases = new ArrayList<SVDBExpr>();
	}
	
	public void setLvalue(SVDBExpr expr) {
		fLvalue = expr;
	}
	
	public SVDBExpr getLvalue() {
		return fLvalue;
	}
	
	public void addAlias(SVDBExpr expr) {
		fAliases.add(expr);
	}
	
	public List<SVDBExpr> getAliases() {
		return fAliases;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_alias(this);
	}
	
}
