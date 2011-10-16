package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBPropertyWeakStrongExpr extends SVDBExpr {
	private boolean				fIsWeak;
	private SVDBExpr			fExpr;
	
	
	public SVDBPropertyWeakStrongExpr() {
		super(SVDBItemType.PropertyWeakStrongExpr);
	}
	
	public void setIsWeak(boolean is_weak) {
		fIsWeak = is_weak;
	}
	
	public boolean getIsWeak() {
		return fIsWeak;
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}

}
