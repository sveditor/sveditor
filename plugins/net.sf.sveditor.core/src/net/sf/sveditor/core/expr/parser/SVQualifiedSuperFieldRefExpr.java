package net.sf.sveditor.core.expr.parser;

public class SVQualifiedSuperFieldRefExpr extends SVExpr {
	
	private SVExpr				fLhs;
	private String				fId;
	
	public SVQualifiedSuperFieldRefExpr(SVExpr lhs, String id) {
		super(SVExprType.QualifiedSuperFieldRef);
		
		fLhs = lhs;
		fId  = id;
	}
	
	public SVExpr getLhs() {
		return fLhs;
	}
	
	public String getId() {
		return fId;
	}

}
