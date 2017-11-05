package net.sf.sveditor.core.builder;

public class SVBuilderOutput implements ISVBuilderOutput {
	private String						fProject;
	private ISVBuilderOutputListener	fListener;
	
	public SVBuilderOutput(
			String						project,
			ISVBuilderOutputListener 	l
			) {
		fProject = project;
		fListener = l;
	}

	@Override
	public void println(String msg) {
		fListener.println(fProject, msg);
	}

	@Override
	public void note(String msg) {
		println("[Note] " + msg);
	}

	@Override
	public void errln(String msg) {
		fListener.errln(fProject, msg);
	}

	@Override
	public void error(String msg) {
		errln("[Error] " + msg);
	}

}
