package net.sf.sveditor.core.scanner;

import net.sf.sveditor.core.scanutils.ScanLocation;


public interface ISVScanner {
	
	void setStmtLocation(ScanLocation location);
	
	ScanLocation getStmtLocation();

}
