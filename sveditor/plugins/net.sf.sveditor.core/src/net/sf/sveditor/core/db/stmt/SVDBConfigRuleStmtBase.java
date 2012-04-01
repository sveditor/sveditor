package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigRuleStmtBase extends SVDBStmt {
	public boolean					fIsLibList;
	public List<SVDBExpr>			fLibUseList;
	public SVDBExpr					fLibCellId;
	public SVDBParamValueAssignList	fParamValueAssign;
	
	public SVDBConfigRuleStmtBase(SVDBItemType type) {
		super(type);
		fLibUseList = new ArrayList<SVDBExpr>();
	}
	
	public void addLib(SVDBExpr lib) {
		fLibUseList.add(lib);
	}
	
	public void setLibCellId(SVDBExpr id) {
		fLibCellId = id;
	}
	
	public void setParamAssign(SVDBParamValueAssignList assign) {
		fParamValueAssign = assign;
	}

}
