package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.preproc.ISVPreProcessor;

public interface ISVDBIndexInt extends ISVDBIndex {
	
	ISVPreProcessor createPreProcScanner(String path);

}
