package net.sf.sveditor.core;

public class SystemOutLineListener implements ILineListener {

	public void line(String l) {
		System.out.println(l);
	}
}
