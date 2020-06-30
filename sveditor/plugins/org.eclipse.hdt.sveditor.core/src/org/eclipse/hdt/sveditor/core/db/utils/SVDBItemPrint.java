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


package org.eclipse.hdt.sveditor.core.db.utils;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBPreProcCond;

public class SVDBItemPrint {
	
	public static void printItem(ISVDBItemBase item) {
		printItem(0, item);
	}
	
	private static void printItem(int indent, ISVDBItemBase item) {
		for (int i=0; i<indent; i++) {
			System.out.print(" ");
		}
		
		System.out.print("" + item.getType());
		if (item instanceof ISVDBNamedItem) {
			System.out.print(" " + ((ISVDBNamedItem)item).getName());
		}
		
		if (item instanceof SVDBPreProcCond) {
			System.out.print(" " + ((SVDBPreProcCond)item).getConditional());
		}
		System.out.println();
		
		if (item instanceof ISVDBScopeItem) {
			for (ISVDBItemBase it : ((ISVDBScopeItem)item).getItems()) {
				printItem(indent+4, it);
			}
		}
	}

}
