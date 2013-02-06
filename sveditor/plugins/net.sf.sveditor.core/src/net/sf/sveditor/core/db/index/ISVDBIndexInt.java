package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.preproc.SVPreProcessor;

public interface ISVDBIndexInt extends ISVDBIndex {
	
	SVPreProcessor createPreProcScanner(String path);

}
