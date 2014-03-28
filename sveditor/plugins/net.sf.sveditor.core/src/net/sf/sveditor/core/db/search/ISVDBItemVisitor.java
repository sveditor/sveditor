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
