package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRefPathExpr extends SVDBExpr {
	
	public SVDBRefPathExpr() {
		super(SVDBItemType.RefPathExpr);
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_ref_path_expr(this);
	}
}
