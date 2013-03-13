package net.sf.sveditor.core.parser;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class SVParserConfig {
	
	public static final String 		ALLOW_INSIDE_Q_WITHOUT_BRACES = "ALLOW_INSIDE_Q_WITHOUT_BRACES";
	
	private static final Map<String, String>		fDescMap;
	private static final Map<String, String>		fShortDescMap;
	
	static {
		fDescMap = new HashMap<String, String>();
		fShortDescMap = new HashMap<String, String>();
		
		fDescMap.put(ALLOW_INSIDE_Q_WITHOUT_BRACES,
				"Allow behavioral <field> inside <queue> expression without " +
				"braces surrounding <queue>. Braces are required by the LRM, " +
				"but some simulators support a relaxed interpretation");
		fShortDescMap.put(ALLOW_INSIDE_Q_WITHOUT_BRACES,
				"Allow <field> inside <queue> expression without braces");
	}
	
	public static Map<String, String> getDescMap() {
		return fDescMap;
	}
	
	public static Set<String> getOptionSet() {
		return fDescMap.keySet();
	}
	
	public static String getShortDesc(String option) {
		return fShortDescMap.get(option);
	}
	
	public String getDesc(String option) {
		return fDescMap.get(option);
	}

	/**
	 * Enables the parser to recognize a statement of the form:
	 * 
	 * if (a inside q)
	 * 
	 * where q is a queue. The LRM-compliant code is:
	 * 
	 * if (a inside {q})
	 * 
	 * VCS appears to allow the first form of the statement.
	 */
	private boolean					fAllowInsideQWithoutBraces = false;
	
	
	public boolean allowInsideQWithoutBraces() {
		return fAllowInsideQWithoutBraces;
	}
	
	public void setAllowInsideQWithoutBraces(boolean a) {
		fAllowInsideQWithoutBraces = a;
	}
	
	public void setOption(String option, boolean en) {
		if (option.equals(ALLOW_INSIDE_Q_WITHOUT_BRACES)) {
			setAllowInsideQWithoutBraces(en);
		}
	}

}
