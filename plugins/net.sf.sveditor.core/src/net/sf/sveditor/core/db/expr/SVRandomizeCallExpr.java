package net.sf.sveditor.core.db.expr;

public class SVRandomizeCallExpr extends SVTFCallExpr {
	private SVConstraintSetExpr				fWithBlock;
	
	public SVRandomizeCallExpr(SVExpr target, String name, SVExpr args[]) {
		super(target, name, args);
		fExprType = SVExprType.RandomizeCall;
	}
	
	public void setWithBlock(SVConstraintSetExpr with) {
		fWithBlock = with;
	}
	
	public SVConstraintSetExpr getWithBlock() {
		return fWithBlock;
	}
	
}
