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


package org.sveditor.core.db.index.old;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;

public class InputStreamCopier {
	private InputStream				fIn;
	private ByteArrayOutputStream	fOut;
	
	public InputStreamCopier(InputStream in) {
		fIn = in;
	}
	
	public InputStream copy() {
		if (fOut == null) {
			byte data[] = new byte[8*1024];
			int size;
			
			fOut = new ByteArrayOutputStream();
			
			try {
				while ((size = fIn.read(data, 0, data.length)) > 0) {
					fOut.write(data, 0, size);
				}
				fIn.close();
				fIn = null;
			} catch (IOException e) {}
		
			/*
			if (fIn != null) {
				try {
					fIn.close();
				} catch (IOException e) {}
			}
			 */
		}

		return new ByteArrayInputStream(fOut.toByteArray());
	}

}
