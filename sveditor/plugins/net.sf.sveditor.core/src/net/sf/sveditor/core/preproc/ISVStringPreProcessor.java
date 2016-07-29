package net.sf.sveditor.core.preproc;

import java.io.InputStream;

public interface ISVStringPreProcessor {
	
	void addListener(IPreProcListener l);
	
	void removeListener(IPreProcListener l);
	
	String preprocess(InputStream in);

}
