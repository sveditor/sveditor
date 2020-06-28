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

import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

public class SVDBFindContentAssistNameMatcher implements ISVDBFindNameMatcher {
	private SVDBItemType			fItemTypes[];
	
	public SVDBFindContentAssistNameMatcher(SVDBItemType ... types) {
		fItemTypes = types;
	}

	public boolean match(ISVDBNamedItem it, String name) {
		if ((fItemTypes.length == 0 || it.getType().isElemOf(fItemTypes)) && it.getName() != null) {
			String it_lower = it.getName().toLowerCase();
			String n_lower = name.toLowerCase();

			if (name.equals("")) {
				// Don't return built-in types
				return (!it_lower.startsWith("__sv_builtin"));
			} else if (it_lower.startsWith(n_lower)) {
				return true;
			} /* else if (it.getType() == SVDBItemType.TypedefStmt && 
					((SVDBTypedefStmt)it).getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
				SVDBTypedefStmt td = (SVDBTypedefStmt)it;
				SVDBTypeInfoEnum ti = (SVDBTypeInfoEnum)td.getTypeInfo();

				Tuple<List<String>, List<String>> enums = ti.getEnumValues();
				for (String en : enums.first()) {
					it_lower = en.toLowerCase();
					if (name.equals("") || it_lower.startsWith(n_lower)) {
						return true;
					}
				}
			} */
		}
		
		return false;
	}
	
}
