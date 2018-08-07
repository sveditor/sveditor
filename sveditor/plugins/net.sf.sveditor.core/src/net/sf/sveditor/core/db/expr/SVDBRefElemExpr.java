package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBRefElemExpr extends SVDBExpr {
	
	public boolean				fStaticRef;
	public SVDBIdentifierExpr	fId;
	public SVDBArrayAccessExpr	fArrayRef;
	// Reference to this element
	public int					fSymRef;
	
	public SVDBRefElemExpr() {
		super(SVDBItemType.RefElemExpr);
	}
	

}
