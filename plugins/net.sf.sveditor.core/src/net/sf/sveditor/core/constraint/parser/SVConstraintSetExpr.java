package net.sf.sveditor.core.constraint.parser;

import java.util.ArrayList;
import java.util.List;

public class SVConstraintSetExpr extends SVExpr {
	private List<SVConstraintExpr>			fConstraintList;
	
	public SVConstraintSetExpr() {
		super(SVExprType.ConstraintSet);
		fConstraintList = new ArrayList<SVConstraintExpr>();
	}
	
	public List<SVConstraintExpr> getConstraintList() {
		return fConstraintList;
	}

}
