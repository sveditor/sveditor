package net.sf.sveditor.core.indent;

public interface ISVIndenter {
	
	void init(ISVIndentScanner scanner);
	
	void indent(SVIndentToken token);
	
	void end();

}
