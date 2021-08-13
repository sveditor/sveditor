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
package org.sveditor.core.vhdl.parser;

import java.util.HashSet;
import java.util.Set;

public class VHDLKeywords {
	
	private static final String fKeywords[] = {
		"abs", "access", "after", "alias", "all", "and", "architecture",
		"array", "assert", "assume", "assume_guarantee", "attribute",
		"begin", "block", "body", "buffer", "bus", "case", "component",
		"configuration", "constant", "context", "cover", "default",
		"disconnect", "downto", "else", "elsif", "end", "entity",
		"exit", "fairness", "file", "for", "force", "function",
		"generate", "generic", "group", "guarded", "if", "impure",
		"in", "inertial", "inout", "is", "label", "library", "linkage",
		"literal", "loop", "map", "mod", "nand", "new", "next", "nor",
		"not", "null", "of", "on", "open", "or", "others", "out",
		"package", "parameter", "port", "postponed", "procedure",
		"process", "property", "protected", "pure", "range", "record",
		"register", "reject", "release", "rem", "report", "restrict",
		"restrict_guarantee", "return", "rol", "ror", "select", "sequence",
		"severity", "signal", "shared", "sla", "sll", "sra", "srl", "strong",
		"subtype", "then", "to", "transport", "type", "unaffected", "units",
		"until", "use", "variable", "vmode", "vprop", "vunit", "wait", "when",
		"while", "with", "xnor", "xor"
	};
	
	private static final Set<String> fKeywordSet;
	
	static {
		fKeywordSet = new HashSet<String>();
		for (int i=0; i<fKeywords.length; i++) {
			fKeywordSet.add(fKeywords[i]);
		}
	}
	
	public static boolean isKeyword(String id) {
		id = id.toLowerCase();
		
		return fKeywordSet.contains(id);
	}
	
	public static Set<String> getKeywords() {
		return fKeywordSet;
	}


}
