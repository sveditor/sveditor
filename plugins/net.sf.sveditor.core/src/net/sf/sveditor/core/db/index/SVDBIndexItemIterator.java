package net.sf.sveditor.core.db.index;

import java.util.Iterator;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBScopeItem;

public class SVDBIndexItemIterator implements ISVDBItemIterator<SVDBItem> {
	private Stack<Iterator<SVDBItem>>	fScopeStack;
	private Iterator<SVDBFile>			fFileIterator;
	private Iterator<SVDBItem>			fScopeIterator;
	
	public SVDBIndexItemIterator(Map<String, SVDBFile> index_items) {
		fFileIterator = index_items.values().iterator();
		fScopeStack = new Stack<Iterator<SVDBItem>>();
		
		/*
		while (fFileIterator.hasNext()) {
			System.out.println("    file=" + fFileIterator.next());
		}
		 */
		fFileIterator = index_items.values().iterator();
	}

	public boolean hasNext() {
		return (fFileIterator.hasNext() 
				|| (!fScopeStack.empty() && fScopeStack.peek().hasNext())
				|| (fScopeIterator != null && fScopeIterator.hasNext()));
	}

	public SVDBItem nextItem() {
		SVDBItem ret = null;
		
		boolean had_next = hasNext();

		for (int i=0; i<16536 && ret == null; i++) {
			if (fScopeIterator != null && fScopeIterator.hasNext()) {
				ret = fScopeIterator.next();
				// System.out.println("Item from scope iterator \"" + ret.getName() + "\"");
				if (ret instanceof SVDBScopeItem) {
					SVDBScopeItem it = (SVDBScopeItem)ret;
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
				// System.out.println("Switch to next file: " + file.getName());
				ret = file;
				
				if (file.getItems().size() > 0) {
					fScopeIterator = file.getItems().iterator();
				}
			}
		}
		
		if (ret == null && had_next) {
			System.out.println("[ERROR] hasNext() returned true and ret == null");
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		return ret;
	}

}
