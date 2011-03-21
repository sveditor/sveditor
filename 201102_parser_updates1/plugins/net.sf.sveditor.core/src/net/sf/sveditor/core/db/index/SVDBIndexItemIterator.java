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
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBIndexItemIterator implements ISVDBItemIterator {
	private ISVDBIndex						fIndex;
	private Stack<Iterator<ISVDBItemBase>>	fScopeStack;
	private Iterator<String>				fFilePathIterator;
	private Iterator<ISVDBItemBase>			fScopeIterator;
	private SVDBFile						fOverrideFile;
	private ISVDBItemBase					fCurrent;
	
	public SVDBIndexItemIterator(List<String> file_list, ISVDBIndex index) {
		fFilePathIterator = file_list.iterator();
		fScopeStack = new Stack<Iterator<ISVDBItemBase>>();
		fIndex = index;
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
	public ISVDBItemBase peekNext(SVDBItemType ... type_list) {
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
	
	private ISVDBItemBase nextItem_int() {
		ISVDBItemBase ret = null;
		
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
			} else if (fFilePathIterator.hasNext()) {
				String path = fFilePathIterator.next();
				SVDBFile file = fIndex.findFile(path);
				
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

	public ISVDBItemBase nextItem(SVDBItemType ... type_list) {
		ISVDBItemBase ret = peekNext(type_list);
		fCurrent = null;
		
		return ret;
	}
}
