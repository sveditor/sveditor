package net.sf.sveditor.core.checker;

import net.sf.sveditor.core.db.SVDBLocation;

public interface ISVDBCheckErrorReporter {
	
	void error(SVDBLocation loc, String msg);

}
