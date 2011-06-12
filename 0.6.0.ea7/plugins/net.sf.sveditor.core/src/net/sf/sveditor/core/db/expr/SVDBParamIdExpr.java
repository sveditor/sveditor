package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

public class SVDBParamIdExpr extends SVDBIdentifierExpr {
	private List<SVDBExpr>				fParamExpr;
	
	public SVDBParamIdExpr() {
		super();
		fParamExpr = new ArrayList<SVDBExpr>();
	}

	public SVDBParamIdExpr(String id) {
		super(id);
		fParamExpr = new ArrayList<SVDBExpr>();
	}

	public List<SVDBExpr> getParamExpr() {
		return fParamExpr;
	}
	
	public void addParamExpr(SVDBExpr expr) {
		fParamExpr.add(expr);
	}
	
}
