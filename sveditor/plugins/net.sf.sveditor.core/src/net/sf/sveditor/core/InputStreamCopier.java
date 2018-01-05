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


package net.sf.sveditor.core;

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
