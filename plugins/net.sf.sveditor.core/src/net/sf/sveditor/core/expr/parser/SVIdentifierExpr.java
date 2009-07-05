package net.sf.sveditor.core.expr.parser;

public class SVIdentifierExpr extends SVExpr {
	private String				fId[];
	private String				fIdStr;
	
	public SVIdentifierExpr(String id[]) {
		super(SVExprType.Identifier);
		
		fId = id;
	}
	
	public String[] getId() {
		return fId;
	}
	
	public String getIdStr() {
		if (fIdStr == null) {
			StringBuilder builder = new StringBuilder();
			for (int i=0; i<fId.length; i++) {
				builder.append(fId[i]);
				if (i+1 < fId.length) {
					builder.append(".");
				}
			}
			fIdStr = builder.toString();
		}
		
		return fIdStr;
	}

}
