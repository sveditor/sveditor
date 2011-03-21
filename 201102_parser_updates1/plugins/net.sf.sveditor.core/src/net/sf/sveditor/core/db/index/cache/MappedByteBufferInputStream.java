package net.sf.sveditor.core.db.index.cache;

import java.io.IOException;
import java.io.InputStream;
import java.nio.MappedByteBuffer;
import java.util.ArrayList;
import java.util.List;

public class MappedByteBufferInputStream extends InputStream {
	private List<MappedByteBuffer>		fBlockList;
	private int							fBlockIdx;
	private byte						fTmp[] = new byte[1];
	
	public MappedByteBufferInputStream() {
		fBlockList = new ArrayList<MappedByteBuffer>();
	}

	@Override
	public int available() throws IOException {
		// TODO Auto-generated method stub
		return super.available();
	}

	@Override
	public void close() throws IOException {
		fBlockList.clear();
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
		return -1;
	}

	@Override
	public int read(byte[] b) throws IOException {
		return read(b, 0, b.length);
	}

}
