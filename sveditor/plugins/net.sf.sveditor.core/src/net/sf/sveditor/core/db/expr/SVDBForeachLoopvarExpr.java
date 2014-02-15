package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBForeachLoopvarExpr extends SVDBExpr {
	public SVDBExpr				fId;
	public List<SVDBExpr>		fLoopVarList;
	
	public SVDBForeachLoopvarExpr() {
		super(SVDBItemType.ForeachLoopvarExpr);
		fLoopVarList = new ArrayList<SVDBExpr>();
	}
	
	public void setId(SVDBExpr id) {
		fId = id;
	}
	
	public void addLoopVar(SVDBExpr loopvar) {
		fLoopVarList.add(loopvar);
	}

}
