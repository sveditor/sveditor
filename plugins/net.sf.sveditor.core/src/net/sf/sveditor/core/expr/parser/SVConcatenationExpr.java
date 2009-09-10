package net.sf.sveditor.core.expr.parser;

import java.util.ArrayList;
import java.util.List;

public class SVConcatenationExpr extends SVExpr {
	private List<SVExpr>			fElems;
	
	public SVConcatenationExpr() {
		super(SVExprType.Concatenation);
		fElems = new ArrayList<SVExpr>();
	}
	
	public List<SVExpr> getElements() {
		return fElems;
	}
	

}
