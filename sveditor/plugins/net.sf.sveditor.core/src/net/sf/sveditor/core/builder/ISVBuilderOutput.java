package net.sf.sveditor.core.builder;

public interface ISVBuilderOutput {
	
	void println(String msg);
	
	void note(String msg);
	
	void errln(String msg);
	
	void error(String msg);
	
}
