package net.sf.sveditor.core.tests;

import java.util.HashMap;
import java.util.Map;

public class SimToolchainUtils {
	public static final String						QUESTA = "questa";
	public static final String						VCS    = "vcs";
	public static final String						NCSIM  = "ncsim";
	
	private static Map<String, ISimToolchain> 		fToolchainMap;
	
	static {
		fToolchainMap = new HashMap<String, ISimToolchain>();
		fToolchainMap.put(QUESTA, new QuestaSimToolChain());
	}

	public static ISimToolchain getToolchain(String id) {
		return fToolchainMap.get(id);
	}

}
