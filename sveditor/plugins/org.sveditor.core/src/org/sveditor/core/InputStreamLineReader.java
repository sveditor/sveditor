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
package org.sveditor.core;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

public class InputStreamLineReader extends Thread {
	private InputStream					fInput;
	private List<ILineListener>			fListeners;
	
	public InputStreamLineReader(
			InputStream				in,
			List<ILineListener> 	l) {
		fInput = in;
		fListeners = new ArrayList<ILineListener>(l);
	}
	
	public InputStreamLineReader(
			InputStream				in,
			ILineListener 			l) {
		fInput = in;
		fListeners = new ArrayList<ILineListener>();
		fListeners.add(l);
	}

	@Override
	public void run() {
		try {
			InputStreamReader rdr = new InputStreamReader(fInput);
			BufferedReader brdr = new BufferedReader(rdr);
			String line;
			
			while ((line = brdr.readLine()) != null) {
				for (ILineListener l : fListeners) {
					synchronized (l) {
						l.line(line);
					}
				}
			}
		} catch (IOException e) {}
	}

}
