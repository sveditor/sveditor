package net.sf.sveditor.core.constraint.parser;

public class SVCondExpr extends SVExpr {
	private SVExpr			fLhs;
	private SVExpr			fMhs;
	private SVExpr			fRhs;
	
	public SVCondExpr(SVExpr lhs, SVExpr mhs, SVExpr rhs) {
		fLhs = lhs;
		fMhs = mhs;
		fRhs = rhs;
	}

}
