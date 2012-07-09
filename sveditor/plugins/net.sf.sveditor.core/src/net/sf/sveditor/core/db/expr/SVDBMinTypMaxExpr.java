package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBMinTypMaxExpr extends SVDBExpr {
	public SVDBExpr			fMin;
	public SVDBExpr			fTyp;
	public SVDBExpr			fMax;
	
	public SVDBMinTypMaxExpr() {
		super(SVDBItemType.MinTypMaxExpr);
	}

	public SVDBMinTypMaxExpr(SVDBExpr min, SVDBExpr typ, SVDBExpr max) {
		this();
		fMin = min;
		fTyp = typ;
		fMax = max;
	}
}
