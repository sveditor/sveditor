package net.sf.sveditor.core.builder;

public class CoreBuilderOutputListener implements ISVBuilderOutputListener {

	@Override
	public void println(String project, String msg) {
		System.out.println("[" + project + "] " + msg);
	}

	@Override
	public void errln(String project, String msg) {
		System.err.println("[" + project + "] " + msg);
	}

}
