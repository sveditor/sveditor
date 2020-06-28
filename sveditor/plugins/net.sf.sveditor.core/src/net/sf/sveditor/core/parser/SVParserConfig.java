/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.parser;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class SVParserConfig {
	
	public static final String 		ALLOW_INSIDE_Q_WITHOUT_BRACES = "ALLOW_INSIDE_Q_WITHOUT_BRACES";
	public static final String 		ALLOW_DIST_INSIDE_PARENS      = "ALLOW_DIST_INSIDE_PARENS";
	
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
		
		fDescMap.put(ALLOW_DIST_INSIDE_PARENS,
				"Allow <expr> dist <dist_list> inside parens. " +
				"The LRM disallows parens around a dist statement");
		fShortDescMap.put(ALLOW_DIST_INSIDE_PARENS,
				"Allow <expr> dist <dist_list> inside parens");
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

	/**
	 * Enable the parser to accept a dist statement of the form:
	 * 
	 * (i == j) -> (k dist {1 := 5, 2 := 10});
	 * 
	 * The LRM doesn't allow this, but some simulators appear to.
	 */
	private boolean					fAllowDistInsideParens = false;
	
	
	public boolean allowInsideQWithoutBraces() {
		return fAllowInsideQWithoutBraces;
	}
	
	public void setAllowInsideQWithoutBraces(boolean a) {
		fAllowInsideQWithoutBraces = a;
	}
	
	public boolean allowDistInsideParens() {
		return fAllowDistInsideParens;
	}
	
	public void setAllowDistInsideParens(boolean en) {
		fAllowDistInsideParens = en;
	}
	
	public void setOption(String option, boolean en) {
		if (option.equals(ALLOW_INSIDE_Q_WITHOUT_BRACES)) {
			setAllowInsideQWithoutBraces(en);
		} else if (option.equals(ALLOW_DIST_INSIDE_PARENS)) {
			setAllowDistInsideParens(en);
		}
	}

}
