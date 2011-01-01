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


package net.sf.sveditor.core.db;

public class SVDBItemPrint {
	
	public static void printItem(SVDBItem item) {
		printItem(0, item);
	}
	
	private static void printItem(int indent, SVDBItem item) {
		for (int i=0; i<indent; i++) {
			System.out.print(" ");
		}
		
		System.out.print("" + item.getType() + " " + item.getName());
		
		if (item instanceof SVDBPreProcCond) {
			System.out.print(" " + ((SVDBPreProcCond)item).getConditional());
		}
		System.out.println();
		
		if (item instanceof ISVDBScopeItem) {
			for (SVDBItem it : ((ISVDBScopeItem)item).getItems()) {
				printItem(indent+4, it);
			}
		}
	}

}
