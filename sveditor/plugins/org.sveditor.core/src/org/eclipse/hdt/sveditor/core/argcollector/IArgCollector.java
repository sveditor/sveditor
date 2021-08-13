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
package org.sveditor.core.argcollector;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.sveditor.core.ILineListener;

public interface IArgCollector {
	
	void addStdoutListener(ILineListener l);
	
	void addStderrListener(ILineListener l);
	
	/**
	 * Executes the compilation command. Returns the 
	 * exit code of the processing command
	 * 
	 * @return 
	 */
	int process(
			File				cwd,
			List<String>		args) throws IOException;

	/**
	 * Returns the document extracted by running the
	 * compilation command
	 * 
	 * @return
	 */
	String getArguments();
}
