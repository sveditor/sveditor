package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

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

}
