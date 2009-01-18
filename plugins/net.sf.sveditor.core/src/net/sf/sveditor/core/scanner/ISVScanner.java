package net.sf.sveditor.core.scanner;

import net.sf.sveditor.core.parser.SVLocation;

public interface ISVScanner {
	
	void setStmtLocation(ScanLocation location);
	
	ScanLocation getStmtLocation();

}
