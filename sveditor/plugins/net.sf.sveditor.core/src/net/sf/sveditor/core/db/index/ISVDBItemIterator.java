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


package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public interface ISVDBItemIterator {
	
	/**
	 * Indicates whether more items of the specified types exist
	 * 
	 * @return
	 */
	boolean hasNext(SVDBItemType ... type_list);
	
	/**
	 * Returns the next item from the iterator
	 * 
	 * @return
	 */
	ISVDBItemBase nextItem(SVDBItemType ... type_list);

}
