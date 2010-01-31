package net.sf.sveditor.core.expr.parser;

import java.util.ArrayList;
import java.util.List;

public class SVInsideExpr extends SVExpr {
	private SVExpr					fLhs;
	private List<SVExpr>			fValueRangeList;
	
	public SVInsideExpr(SVExpr lhs) {
		super(SVExprType.Inside);
		fLhs = lhs;
		fValueRangeList = new ArrayList<SVExpr>();
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public List<SVExpr> getValueRangeList() {
		return fValueRangeList;
	}

}
