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

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

public class SVFileBuffer extends InputStream {
	private static final int				fPageSize = 4096;
	private InputStream						fIn;
	private long							fReadTime;
	private List<byte[]>					fPageList;
	private int								fPageListIdx;
	private byte[]							fCurrPage;
	private int								fPageIdx;
	private int								fPageLen;
	private int								fLastPageLength;
	private static final boolean			fFullRead = true;
	
	public SVFileBuffer(InputStream in) {
		if (fFullRead) {
			fPageList = new ArrayList<byte[]>();
		}
		init(in);
	}
	
	public long init(InputStream in) {
		byte page[] = new byte[fPageSize];
		int len = -1;
		
		fIn = in;
		if (fFullRead) {
		fPageList.clear();
		long start = System.currentTimeMillis();
	
		try {
			while ((len = in.read(page, 0, fPageSize)) == fPageSize) {
				fPageList.add(page);
				page = new byte[fPageSize];
			}
		} catch (IOException e) {}
		
		if (len > 0) {
			fPageList.add(page);
			fLastPageLength = len;
		}
		
		long end = System.currentTimeMillis();
		fReadTime = (end-start);
	
		if (fPageList.size() > 0) {
			fCurrPage = fPageList.get(0);
			fPageListIdx = 0;
			fPageIdx = 0;
			if (fPageList.size() > 1) {
				fPageLen = fPageSize;
			} else {
				fPageLen = fLastPageLength;
			}
		}
		} else { // Incremental read
		try {
			len = in.read(page, 0, fPageSize);
		} catch (IOException e) {}
			fCurrPage = page;
			fPageLen = len;

		}
		
		return fReadTime;
	}
	
	public long getReadTime() {
		return fReadTime;
	}

	@Override
	public int read() throws IOException {
		if (fFullRead) {
		if (fPageIdx >= fPageLen) {
			// Switch to new page or quit
			if (fPageListIdx+1 >= fPageList.size()) {
				return -1;
			}
			fPageListIdx++;
			fCurrPage = fPageList.get(fPageListIdx);
			fPageIdx = 0;
			if (fPageListIdx+1 < fPageList.size()) {
				// Not the last page
				fPageLen = fPageSize;
			} else {
				fPageLen = fLastPageLength;
			}
		}
		
		return fCurrPage[fPageIdx++];
		} else {
			if (fPageIdx >= fPageLen) {
				int len=0;
				
				try {
					len = fIn.read(fCurrPage, 0, fPageSize);
				} catch (IOException e) {}
				fPageIdx = 0;
				fPageLen = len;
				
				if (len <= 0) {
					return -1;
				}
			}
			
			return fCurrPage[fPageIdx++];
		}
	}

	@Override
	public void close() throws IOException {
		fIn.close();
	}
	
}
