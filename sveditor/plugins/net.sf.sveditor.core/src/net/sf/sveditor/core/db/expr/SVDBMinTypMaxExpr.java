package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.ISVDBVisitor;
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
	
	public SVDBExpr getMin() {
		return fMin;
	}
	
	public SVDBExpr getTyp() {
		return fTyp;
	}
	
	public SVDBExpr getMax() {
		return fMax;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_min_typ_max_expr(this);
	}
	
}
