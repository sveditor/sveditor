package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBOpenRangeListExpr extends SVDBExpr {
	public List<SVDBExpr>			fRangeList;
	
	public SVDBOpenRangeListExpr() {
		super(SVDBItemType.OpenRangeListExpr);
		fRangeList = new ArrayList<SVDBExpr>();
	}
	
	public List<SVDBExpr> getRangeList() {
		return fRangeList;
	}

}
