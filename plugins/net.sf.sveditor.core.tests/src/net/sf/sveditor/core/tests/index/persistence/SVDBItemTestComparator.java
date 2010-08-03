package net.sf.sveditor.core.tests.index.persistence;

import java.util.Stack;

import junit.framework.TestCase;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBItemTestComparator {
	private Stack<SVDBScopeItem>			fScopeStack;
	
	public SVDBItemTestComparator() {
		fScopeStack = new Stack<SVDBScopeItem>();
	}
	
	public void compare(SVDBScopeItem i1, SVDBScopeItem i2) {
		// Ensure names / types are equal
		TestCase.assertEquals("Failed to compare scope type @ " + 
				getScope(i1), i1.getType(), i2.getType());
		TestCase.assertEquals("Failed to compare scope name @ " + 
				getScope(i1), i1.getName(), i2.getName());
		TestCase.assertEquals("Sub-Elements are different @ " +
				getScope(i1), i1.getItems().size(), i2.getItems().size());
		
		// First, see if we can recurse deeper
		for (int i=0; i<i1.getItems().size(); i++) {
			if ((i1.getItems().get(i) instanceof SVDBScopeItem) ||
					(i2.getItems().get(i) instanceof SVDBScopeItem)) {
				TestCase.assertEquals(true, (i1.getItems().get(i) instanceof SVDBScopeItem));
				TestCase.assertEquals(true, (i2.getItems().get(i) instanceof SVDBScopeItem));
				fScopeStack.push(i1);
				compare((SVDBScopeItem)i1.getItems().get(i), (SVDBScopeItem)i2.getItems().get(i));
				fScopeStack.pop();
			}
		}
		
		// Next, compare the non-scope elements at this level
		for (int i=0; i<i1.getItems().size(); i++) {
			if (!(i1.getItems().get(i) instanceof SVDBScopeItem)) {
				SVDBItem i1_t = i1.getItems().get(i);
				SVDBItem i2_t = i2.getItems().get(i);
				
				if (!i1_t.equals(i2_t)) {
					i1_t.equals(i2_t);
					TestCase.assertTrue("Element " + (i1.getItems().get(i).getType()) + 
							" is different @ " + getScope(i1.getItems().get(i)),
							i1_t.equals(i2_t));
				}
			}
		}

		// Finally, compare scopes
		for (int i=0; i<i1.getItems().size(); i++) {
			if ((i1.getItems().get(i) instanceof SVDBScopeItem)) {
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
	
	private String getScope(SVDBItem leaf) {
		StringBuilder ret = new StringBuilder();
		
		for (SVDBItem it : fScopeStack) {
			ret.append(it.getName());
			ret.append(".");
		}
		ret.append(leaf.getName());
		
		return ret.toString();
	}
}
