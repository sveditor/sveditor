/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.core.db.index;

import java.util.Iterator;

import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBItemType;

/**
 * Iterator that iterates over a list of index item iterators
 * @author ballance
 *
 */
class SVDBIndexItemItIterator /* implements ISVDBItemIterator */ {
	
	private Iterator<ISVDBIndexIterator>		fIterator;
	private ISVDBItemIterator					fCurrent;
	private IProgressMonitor					fMonitor;
	
	public SVDBIndexItemItIterator(Iterator<ISVDBIndexIterator> it, IProgressMonitor monitor) {
		fIterator = it;
		fMonitor = monitor;
	}

	/*
	public boolean hasNext(SVDBItemType... type_list) {
		while (fCurrent != null || fIterator.hasNext()) {
			
			if (fCurrent == null) {
				fCurrent = fIterator.next().getItemIterator(fMonitor);
			}
			
			if (!fCurrent.hasNext(type_list)) {
				fCurrent = null;
				continue;
			} else {
				break;
			}
		}
		
		return (fCurrent != null && fCurrent.hasNext(type_list));
	}

	public ISVDBItemBase nextItem(SVDBItemType... type_list) {
		ISVDBItemBase ret = null;
		
		while (fCurrent != null || fIterator.hasNext()) {
			
			if (fCurrent == null) {
				fCurrent = fIterator.next().getItemIterator(fMonitor);
			}
			
			if ((ret = fCurrent.nextItem(type_list)) == null) {
				fCurrent = null;
				continue;
			} else {
				break;
			}
		}
		
		return ret;
	}
	 */
}