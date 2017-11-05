package net.sf.sveditor.core.builder;

public class SafeSVBuilderOutput implements ISVBuilderOutput {
	private ISVBuilderOutput		fOut;
	
	public SafeSVBuilderOutput(ISVBuilderOutput out) {
		fOut = out;
	}

	@Override
	public void println(String msg) {
		if (fOut != null) {
			fOut.println(msg);
		}
	}

	@Override
	public void note(String msg) {
		if (fOut != null) {
			fOut.note(msg);
		}
	}

	@Override
	public void errln(String msg) {
		if (fOut != null) {
			fOut.errln(msg);
		} 
	}
	
	public void error(String msg) {
		if (fOut != null) {
			fOut.error(msg);
		}
	}

}
