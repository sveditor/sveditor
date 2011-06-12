package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBGenerateIf extends SVDBChildItem implements ISVDBAddChildItem {
	@SVDBDoNotSaveAttr
	private int				fAddIdx;
	private SVDBExpr		fExpr;
	private ISVDBChildItem	fIfBody;
	private ISVDBChildItem	fElseBody;
	
	public SVDBGenerateIf() {
		super(SVDBItemType.GenerateIf);
	}
	
	public void setExpr(SVDBExpr expr) {
		fExpr = expr;
	}
	
	public SVDBExpr getExpr() {
		return fExpr;
	}
	
	public ISVDBChildItem getIfBody() {
		return fIfBody;
	}
	
	public ISVDBChildItem getElseBody() {
		return fElseBody;
	}

	public void addChildItem(ISVDBChildItem item) {
		if (fAddIdx == 0) {
			fIfBody = item;
		} else if (fAddIdx == 1) {
			fElseBody = item;
		}
		fAddIdx++;
	}

	
}
