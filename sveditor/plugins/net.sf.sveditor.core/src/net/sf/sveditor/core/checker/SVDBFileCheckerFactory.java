package net.sf.sveditor.core.checker;

import net.sf.sveditor.core.db.index.ISVDBMarkerMgr;
import net.sf.sveditor.core.preproc.ISVPreProcFileMapper;

public class SVDBFileCheckerFactory {
	
	public static ISVDBChecker create(
			ISVDBMarkerMgr 			marker_mgr,
			ISVPreProcFileMapper 	mapper) {
	
		SVDBFileChecker checker = new SVDBFileChecker(marker_mgr, mapper);
		SVDBMethodVarRefChecker.add(checker);
		
		return checker;
	}

}
