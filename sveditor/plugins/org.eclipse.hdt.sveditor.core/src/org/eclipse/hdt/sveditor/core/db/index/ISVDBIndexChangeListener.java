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


package org.eclipse.hdt.sveditor.core.db.index;

import org.eclipse.hdt.sveditor.core.db.SVDBFile;

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
