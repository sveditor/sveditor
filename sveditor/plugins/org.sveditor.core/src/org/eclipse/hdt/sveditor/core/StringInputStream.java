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


package org.sveditor.core;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;

public class StringInputStream extends InputStream {
	private StringReader			fReader;
	private int						fLastC;
	
	public StringInputStream(String content) {
		fReader = new StringReader(content);
		fLastC = 0;
	}

	@Override
	public int read() throws IOException {
		int ret = -1;
		try {
			ret = fReader.read();
		} catch (IOException e) { }
		
		fLastC = ret;
		
		return ret;
	}
	
	public void close() throws IOException {
		fReader.close();
	}
	
	public synchronized void mark(int readLimit) {
		try {
			fReader.mark(readLimit);
		} catch (IOException e) {
		}
	}
	
	public boolean markSupported() {
		return fReader.markSupported();
	}

	public synchronized void reset() throws IOException {
		fReader.reset();
	}

	@Override
	public int available() throws IOException {
		return (fLastC != -1)?1:0;
	}
	
}
