package net.sf.sveditor.core.preproc;

import java.io.InputStream;

public interface ISVStringPreProcessor {
	
	void addListener(ISVPreProcListener l);
	
	void removeListener(ISVPreProcListener l);

	/**
	 * Specifies whether `line directives should be emitted
	 * 
	 * @param emit
	 */
	void setEmitLineDirectives(boolean emit);
	
	String preprocess(InputStream in);

}
