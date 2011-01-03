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


package net.sf.sveditor.core.tests.index.persistence;

import java.util.Stack;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBLocatedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBItem;

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
				getScope(i1), i1.getName(), i2.getName());
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
				SVDBItem i1_t = i1.getItems().get(i);
				SVDBItem i2_t = i2.getItems().get(i);
				
				if (!i1_t.equals(i2_t)) {
					i1_t.equals(i2_t);
					System.out.println("Element i1: " + i1_t.getType() + ":" + i1_t.getName() + 
							" ; Element i2: " + i2_t.getType() + ":" + i2_t.getName());
					System.out.println("    i1: " + i1_t.getLocation() + " i2: " + i2_t.getLocation());
					TestCase.assertTrue("Element " + (i1.getItems().get(i).getType()) + 
							" is different @ " + getScope(i1.getItems().get(i)),
							i1_t.equals(i2_t));
				}
			}
		}

		// Finally, compare scopes
		for (int i=0; i<i1.getItems().size(); i++) {
			if ((i1.getItems().get(i) instanceof ISVDBScopeItem)) {
				SVDBItem i1_t = i1.getItems().get(i);
				SVDBItem i2_t = i2.getItems().get(i);
				if (!i1_t.equals(i2_t)) {
					i1_t.equals(i2_t);
					
					TestCase.assertTrue("Scope " +  (i1.getItems().get(i).getType()) +
							" is different @ " +  getScope(i1.getItems().get(i)),
							i1_t.equals(i2_t));
				}
			}
		}
	}
	
	private String getScope(ISVDBLocatedItem leaf) {
		StringBuilder ret = new StringBuilder();
		
		for (ISVDBScopeItem it : fScopeStack) {
			ret.append(it.getName());
			ret.append(".");
		}
		ret.append(leaf.getName());
		
		return ret.toString();
	}
}
