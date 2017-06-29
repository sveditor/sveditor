package net.sf.sveditor.core.checker;

import net.sf.sveditor.core.db.ISVDBItemBase;

public interface ISVDBCheckVisitor {
	
	void visit(
			ISVDBCheckErrorReporter		err_reporter,
			ISVDBItemBase 				it);

}
