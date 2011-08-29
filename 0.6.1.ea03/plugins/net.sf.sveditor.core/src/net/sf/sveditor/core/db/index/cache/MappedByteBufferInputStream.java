/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index.cache;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.channels.FileChannel.MapMode;

public class MappedByteBufferInputStream extends InputStream {
	private RandomAccessFile			fIn;
	private ByteBuffer					fByteBuffer;
	private int							fBufferIdx;
	private int							fBufferMax;
	private byte						fTmp[] = new byte[1];
	
	public MappedByteBufferInputStream(File path) throws IOException {
		fIn = new RandomAccessFile(path, "r");

		FileChannel channel = fIn.getChannel();
		fByteBuffer = channel.map(MapMode.READ_ONLY, 0, channel.size());
		fBufferMax = (int)channel.size();
		fBufferIdx = 0;
	}

	@Override
	public int available() throws IOException {
		return (fByteBuffer.limit()-fBufferIdx);
	}

	@Override
	public void close() throws IOException {
		fIn.close();
	}

	@Override
	public boolean markSupported() {
		return false;
	}

	@Override
	public int read() throws IOException {
		int ret = read(fTmp, 0, 1);
		
		if (ret <= 0) {
			return -1;
		} else {
			return fTmp[0];
		}
	}

	@Override
	public int read(byte[] b, int off, int len) throws IOException {
		int ret = -1;

		if (fByteBuffer.remaining() > 0) {
			ret = (fByteBuffer.remaining() >= len)?len:fByteBuffer.remaining();
			fByteBuffer.get(b, off, ret);
			System.out.println("Read " + ret + " bytes");
		}
		return ret;
	}

	@Override
	public int read(byte[] b) throws IOException {
		return read(b, 0, b.length);
	}

}
