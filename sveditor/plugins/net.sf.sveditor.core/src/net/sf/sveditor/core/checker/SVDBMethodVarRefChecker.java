package net.sf.sveditor.core.checker;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.expr_utils.SVContentAssistExprVisitor;

public class SVDBMethodVarRefChecker implements ISVDBCheckVisitor {

	@Override
	public void visit(
			ISVDBCheckErrorReporter 	err_reporter, 
			ISVDBItemBase 				it) {
		SVDBTask t = (SVDBTask)it; // Same for most purposes

//		SVContentAssistExprVisitor visitor = new SVContentAssistExprVisitor(
//				scope, name_matcher, index_it)
//		t.getChildren()

	}

	public static void add(SVDBFileChecker c) {
		SVDBMethodVarRefChecker v = new SVDBMethodVarRefChecker();
		for (SVDBItemType t : new SVDBItemType[] {SVDBItemType.Function, SVDBItemType.Task}) {
			c.addChecker(t, v);
		}
	}
}
