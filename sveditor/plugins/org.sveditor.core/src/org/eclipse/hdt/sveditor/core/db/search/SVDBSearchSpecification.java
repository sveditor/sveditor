/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db.search;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SVDBSearchSpecification {
	private String			fExpr;
	private boolean			fCaseSensitive;
	private boolean			fRegExp;
	private SVDBSearchType	fType;
	private SVDBSearchUsage	fUsage;
	private Pattern			fPattern;
	
	public SVDBSearchSpecification(
			String 				expr,
			boolean				case_sensitive,
			boolean				reg_exp,
			SVDBSearchType		type,
			SVDBSearchUsage		usage) {
		fExpr 			= expr;
		fCaseSensitive 	= case_sensitive;
		fRegExp			= reg_exp;
		fType			= type;
		fUsage			= usage;
		
		int flags = 0;
		if (!fCaseSensitive) {
			flags |= Pattern.CASE_INSENSITIVE;
		}
		if (!fRegExp) {
			// Should reformat to accept '*' and '?'
			flags |= Pattern.LITERAL;
		}
		
		fPattern = Pattern.compile(expr, flags);
	}

	public SVDBSearchSpecification(
			String 		expr,
			boolean		case_sensitive,
			boolean		reg_exp) {
		this(expr, case_sensitive, reg_exp, SVDBSearchType.Type, 
				SVDBSearchUsage.All);
	}

	public void setSearchType(SVDBSearchType type) {
		fType = type;
	}
	
	public SVDBSearchType getSearchType() {
		return fType;
	}
	
	public void setSearchUsage(SVDBSearchUsage usage) {
		fUsage = usage;
	}
	
	public SVDBSearchUsage getSearchUsage() {
		return fUsage;
	}
	
	public String getExpr() {
		return fExpr;
	}
	
	public boolean isRegExp() {
		return fRegExp;
	}
	
	public boolean isCaseSensitive() {
		return fCaseSensitive;
	}
	
	public boolean match(String name) {
		Matcher m = fPattern.matcher(name);
		// Only insist on a full match if the user specified a regular expression.
		// Otherwise, accept prefix matches
		if (fRegExp) {
			return m.matches();
		} else {
			return (m.find() && m.start() == 0);
		}
		// return fPattern.matcher(name).matches();
	}

}
