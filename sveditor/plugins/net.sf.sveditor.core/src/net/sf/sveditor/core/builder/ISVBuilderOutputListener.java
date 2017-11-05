package net.sf.sveditor.core.builder;

public interface ISVBuilderOutputListener {

	void println(String project, String msg);

	void errln(String project, String msg);
}
