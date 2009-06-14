package net.sf.sveditor.core.constraint.parser;

public class SVIdentifierExpr extends SVExpr {
	private String				fId[];
	
	public SVIdentifierExpr(String id[]) {
		super(SVExprType.Identifier);
		
		fId = id;
	}
	
	public String[] getId() {
		return fId;
	}

}
