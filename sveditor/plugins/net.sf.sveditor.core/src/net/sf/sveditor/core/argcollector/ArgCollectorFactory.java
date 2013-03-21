package net.sf.sveditor.core.argcollector;

public class ArgCollectorFactory {
	
	public static IArgCollector create() {
		IArgCollector ret = null;
		
		String os = System.getProperty("os.name");
		
		if (os.toLowerCase().contains("win")) {
			ret = new WindowsArgCollector();
		} else {
			// Default to Linux
			ret = new LinuxArgCollector();
		}
		
		return ret;
	}

}
