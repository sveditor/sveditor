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


package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBFile;

/**
 * Listener interface that notifies about index events. 
 * Note: to avoid thread deadlock, listener-method
 * implementations should not call the index directly.
 * 
 * @author ballance
 *
 */
public interface ISVDBIndexChangeListener {
	
	int FILE_ADDED   = 1;
	int FILE_REMOVED = 2;
	int FILE_CHANGED = 3;

	void index_event(SVDBIndexChangeEvent e);
	
//	void index_changed(int reason, SVDBFile file);
//	
//	void index_rebuilt();

}
