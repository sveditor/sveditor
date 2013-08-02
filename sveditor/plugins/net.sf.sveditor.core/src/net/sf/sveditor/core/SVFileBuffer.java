package net.sf.sveditor.core;

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
	
	public SVFileBuffer(InputStream in) {
		fPageList = new ArrayList<byte[]>();
		init(in);
	}
	
	public long init(InputStream in) {
		long start = System.currentTimeMillis();
		byte page[] = new byte[fPageSize];
		int len = -1;
		
		fIn = in;
		fPageList.clear();
	
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
		
		return fReadTime;
	}
	
	public long getReadTime() {
		return fReadTime;
	}

	@Override
	public int read() throws IOException {
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
	}

	@Override
	public void close() throws IOException {
		fIn.close();
	}
	
}
