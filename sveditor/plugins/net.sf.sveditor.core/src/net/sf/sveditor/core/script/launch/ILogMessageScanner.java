package net.sf.sveditor.core.script.launch;

import net.sf.sveditor.core.ILineListener;

public interface ILogMessageScanner extends ILineListener {
	
	void init(ILogMessageScannerMgr mgr);

	/**
	 * Indicates whether this scanner can produce changes in working directory
	 * 
	 * @return
	 */
	boolean providesDirectory();

}
