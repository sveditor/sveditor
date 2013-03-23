package net.sf.sveditor.core.argcollector;

public class ArgCollectorFactory {
	
	public static IArgCollector create() {
		return new BaseArgCollector();
	}

}
