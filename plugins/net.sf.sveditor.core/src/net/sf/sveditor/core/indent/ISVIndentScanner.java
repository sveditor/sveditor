package net.sf.sveditor.core.indent;

public interface ISVIndentScanner {
	
	SVIndentToken next();
	
	SVIndentToken current();

}
