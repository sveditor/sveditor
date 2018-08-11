package net.sf.sveditor.core.db.stmt;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.expr.SVDBExpr;

public class SVDBConfigDesignStmt extends SVDBStmt {
	public List<SVDBExpr>				fCellIdentifiers;
	
	public SVDBConfigDesignStmt() {
		super(SVDBItemType.ConfigDesignStmt);
		fCellIdentifiers = new ArrayList<SVDBExpr>();
	}
	
	public void addCellIdentifier(SVDBExpr id) {
		fCellIdentifiers.add(id);
	}
	
	public List<SVDBExpr> getCellIdentifiers() {
		return fCellIdentifiers;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_config_design_stmt(this);
	}

}
