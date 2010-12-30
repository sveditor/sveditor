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


package net.sf.sveditor.core.db.index;

import java.util.Iterator;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBIndexItemIterator implements ISVDBItemIterator {
	private Stack<Iterator<SVDBItem>>	fScopeStack;
	private Iterator<SVDBFile>			fFileIterator;
	private Iterator<SVDBItem>			fScopeIterator;
	private SVDBFile					fOverrideFile;
	private SVDBItem					fCurrent;
	
	public SVDBIndexItemIterator(Map<String, SVDBFile> index_items) {
		fFileIterator = index_items.values().iterator();
		fScopeStack = new Stack<Iterator<SVDBItem>>();
		
		fFileIterator = index_items.values().iterator();
	}
	
	public void setOverride(SVDBFile file) {
		fOverrideFile = file;
	}
	
	/**
	 * For now, we'll just filter out the un-interesting items.
	 * TODO: Future would involve filtering more intelligently / efficiently
	 * 
	 * @param type_list
	 * @return
	 */
	public SVDBItem peekNext(SVDBItemType ... type_list) {
		while (true) {
			if (fCurrent == null) {
				fCurrent = nextItem_int();
			}

			if (fCurrent != null) {
				if (fCurrent.getType().isElemOf(type_list)) {
					break;
				} else {
					fCurrent = null;
				}
			} else {
				break;
			}
		}
		
		return fCurrent;
	}
	
	public boolean hasNext(SVDBItemType ... type_list) {
		return (peekNext(type_list) != null);
	}
	
	private SVDBItem nextItem_int() {
		SVDBItem ret = null;
		
//		boolean had_next = hasNext();

		for (int i=0; i<16536 && ret == null; i++) {
			if (fScopeIterator != null && fScopeIterator.hasNext()) {
				ret = fScopeIterator.next();
				
				// System.out.println("Item from scope iterator \"" + ret.getName() + "\"");
				if (ret instanceof ISVDBScopeItem) {
					ISVDBScopeItem it = (ISVDBScopeItem)ret;
					if (it.getItems().size() > 0) {
						// System.out.println("Push new scope \"" + ret.getName() + "\"");
						if (fScopeIterator.hasNext()) {
							fScopeStack.push(fScopeIterator);
						}
						fScopeIterator = it.getItems().iterator();
					}
				}
			} else if (!fScopeStack.empty()) {
				fScopeIterator = fScopeStack.pop();
			} else if (fFileIterator.hasNext()) {
				SVDBFile file = fFileIterator.next();
				
				// Replace the file from the database with the override file
				if (fOverrideFile != null &&
						file.getFilePath().equals(fOverrideFile.getFilePath())) {
					file = fOverrideFile;
				}
				
				// System.out.println("Switch to next file: " + file.getName());
				ret = file;
				
				if (file.getItems().size() > 0) {
					fScopeIterator = file.getItems().iterator();
				}
			}
		}

		/*
		if (ret == null && had_next) {
			System.out.println("[ERROR] hasNext() returned true and ret == null");
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		 */

		return ret;
	}

	public SVDBItem nextItem(SVDBItemType ... type_list) {
		SVDBItem ret = peekNext(type_list);
		fCurrent = null;
		
		return ret;
	}
}
