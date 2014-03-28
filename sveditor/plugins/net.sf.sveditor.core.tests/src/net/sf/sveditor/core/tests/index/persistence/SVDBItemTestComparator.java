/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.persistence;

import java.util.Stack;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBItemTestComparator {
	private Stack<ISVDBScopeItem>			fScopeStack;
	
	public SVDBItemTestComparator() {
		fScopeStack = new Stack<ISVDBScopeItem>();
	}
	
	public void compare(ISVDBScopeItem i1, ISVDBScopeItem i2) {
		// Ensure names / types are equal
		TestCase.assertEquals("Failed to compare scope type @ " + 
				getScope(i1), i1.getType(), i2.getType());
		TestCase.assertEquals("Failed to compare scope name @ " + 
				getScope(i1), SVDBItem.getName(i1), SVDBItem.getName(i2));
		TestCase.assertEquals("Sub-Elements are different @ " +
				getScope(i1), i1.getItems().size(), i2.getItems().size());
		
		// First, see if we can recurse deeper
		for (int i=0; i<i1.getItems().size(); i++) {
			if ((i1.getItems().get(i) instanceof ISVDBScopeItem) ||
					(i2.getItems().get(i) instanceof ISVDBScopeItem)) {
				TestCase.assertEquals(true, (i1.getItems().get(i) instanceof ISVDBScopeItem));
				TestCase.assertEquals(true, (i2.getItems().get(i) instanceof ISVDBScopeItem));
				fScopeStack.push(i1);
				compare((ISVDBScopeItem)i1.getItems().get(i), (ISVDBScopeItem)i2.getItems().get(i));
				fScopeStack.pop();
			}
		}
		
		// Next, compare the non-scope elements at this level
		for (int i=0; i<i1.getItems().size(); i++) {
			if (!(i1.getItems().get(i) instanceof ISVDBScopeItem)) {
				ISVDBItemBase i1_t = i1.getItems().get(i);
				ISVDBItemBase i2_t = i2.getItems().get(i);
				
				if (!i1_t.equals(i2_t)) {
					i1_t.equals(i2_t);
					System.out.println("Element i1: " + i1_t.getType() + ":" + SVDBItem.getName(i1_t) + 
							" ; Element i2: " + i2_t.getType() + ":" + SVDBItem.getName(i2_t));
					System.out.println("    i1: " + i1_t.getLocation() + " i2: " + i2_t.getLocation());
					SVDBItemType it = i1.getItems().get(i).getType();
					String type_name;
					type_name = "" + it;
					type_name += " " + SVDBItem.getName(i1.getItems().get(i));
					TestCase.assertTrue("Element " + type_name  + 
							" is different @ " + getScope(i1.getItems().get(i)),
							i1_t.equals(i2_t));
				}
			}
		}

		// Finally, compare scopes
		for (int i=0; i<i1.getItems().size(); i++) {
			if ((i1.getItems().get(i) instanceof ISVDBScopeItem)) {
				ISVDBItemBase i1_t = i1.getItems().get(i);
				ISVDBItemBase i2_t = i2.getItems().get(i);
				if (!i1_t.equals(i2_t)) {
					i1_t.equals(i2_t);
					
					TestCase.assertTrue("Scope " +  (i1.getItems().get(i).getType()) +
							" is different @ " +  getScope(i1.getItems().get(i)),
							i1_t.equals(i2_t));
				}
			}
		}
	}
	
	private String getScope(ISVDBItemBase leaf) {
		StringBuilder ret = new StringBuilder();
		
		for (ISVDBScopeItem it : fScopeStack) {
			ret.append(SVDBItem.getName(it));
			ret.append(".");
		}
		ret.append(SVDBItem.getName(leaf));
		
		return ret.toString();
	}
}
