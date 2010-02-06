/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypedef;

public class SVDBFindContentAssistNameMatcher implements ISVDBFindNameMatcher {

	public boolean match(SVDBItem it, String name) {
		if (it.getName() != null) {
			String it_lower = it.getName().toLowerCase();
			String n_lower = name.toLowerCase();

			if (name.equals("") || it_lower.startsWith(n_lower)) {
				return true;
			} else if (it.getType() == SVDBItemType.Typedef && ((SVDBTypedef)it).isEnumType()) {
				SVDBTypedef td = (SVDBTypedef)it;
				
				for (String n : td.getEnumNames()) {
					it_lower = n.toLowerCase();
					if (name.equals("") || it_lower.startsWith(n_lower)) {
						return true;
					}
				}
			}
		}
		
		return false;
	}
	
}
