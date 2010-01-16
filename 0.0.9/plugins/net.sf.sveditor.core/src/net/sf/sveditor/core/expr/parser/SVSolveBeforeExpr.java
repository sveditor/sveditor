package net.sf.sveditor.core.expr.parser;

import java.util.ArrayList;
import java.util.List;

public class SVSolveBeforeExpr extends SVConstraintExpr {
	private List<String>				fSolveBeforeList;
	private List<String>				fSolveAfterList;
	
	public SVSolveBeforeExpr() {
		super(SVExprType.SolveBefore);
		fSolveBeforeList = new ArrayList<String>();
		fSolveAfterList = new ArrayList<String>();
	}
	
	public List<String> getSolveBeforeList() {
		return fSolveBeforeList;
	}
	
	public List<String> getSolveAfterList() {
		return fSolveAfterList;
	}

}
