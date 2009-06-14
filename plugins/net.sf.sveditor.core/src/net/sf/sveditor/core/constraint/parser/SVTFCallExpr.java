package net.sf.sveditor.core.constraint.parser;

public class SVTFCallExpr extends SVExpr {
	private SVExpr				fTarget;
	private String				fName;
	private SVExpr				fArgs[];

	public SVTFCallExpr(SVExpr target, String id, SVExpr args[]) {
		super(SVExprType.TFCall);

		fTarget = target;
		fName	= id;
		fArgs   = args;
	}
	
	public SVExpr getTarget() {
		return fTarget;
	}
	
	public String getName() {
		return fName;
	}
	
	public SVExpr [] getArgs() {
		return fArgs;
	}
	
}
