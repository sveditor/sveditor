/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.script.launch;

import net.sf.sveditor.core.ILineListener;

public interface ILogMessageScanner extends ILineListener {
	
	void init(ILogMessageScannerMgr mgr);

	/**
	 * Indicates whether this scanner can produce changes in working directory
	 * 
	 * @return
	 */
	boolean providesDirectory();

	// Indicates the end of the log file
	// Multi-line parsers can use this to propagate any trailing messages
	void close();
}
