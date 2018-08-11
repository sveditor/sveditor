package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBVisitor;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBAssociativeArrayAssignExpr extends SVDBExpr {
	public List<SVDBAssociativeArrayElemAssignExpr>		fElements;
	
	public SVDBAssociativeArrayAssignExpr() {
		super(SVDBItemType.AssociativeArrayAssignExpr);
		fElements = new ArrayList<SVDBAssociativeArrayElemAssignExpr>();
	}
	
	public void addElement(SVDBAssociativeArrayElemAssignExpr elem) {
		fElements.add(elem);
	}
	
	public List<SVDBAssociativeArrayElemAssignExpr> getElements() {
		return fElements;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_associative_array_assign_expr(this);
	}

	
}
