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


package net.sf.sveditor.core.db.search;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;

public interface ISVDBItemVisitor {
	
	int CONTINUE                  = 0;
	int DONT_RECURSE              = 1;
	int CANCEL                    = 2;
	
	/**
	 * Called to process the specified item
	 * 
	 * @param index The index that contains this item
	 * @param item
	 * @return
	 */
	int accept(ISVDBIndex index, SVDBItem item);

}
