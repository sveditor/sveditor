package net.sf.sveditor.core.expr.parser;

import java.util.ArrayList;
import java.util.List;

public class SVConstraintSetExpr extends SVExpr {
	private List<SVExpr>				fConstraintList;
	
	public SVConstraintSetExpr() {
		super(SVExprType.ConstraintSet);
		fConstraintList = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getConstraintList() {
		return fConstraintList;
	}

}
