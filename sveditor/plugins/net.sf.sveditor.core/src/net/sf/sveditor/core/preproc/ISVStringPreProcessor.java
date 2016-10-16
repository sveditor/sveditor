package net.sf.sveditor.core.preproc;

import java.io.InputStream;

public interface ISVStringPreProcessor {
	
	void addListener(IPreProcListener l);
	
	void removeListener(IPreProcListener l);

	/**
	 * Specifies whether `line directives should be emitted
	 * 
	 * @param emit
	 */
	void setEmitLineDirectives(boolean emit);
	
	String preprocess(InputStream in);

}
