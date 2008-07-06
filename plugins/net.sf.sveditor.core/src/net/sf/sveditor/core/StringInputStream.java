package net.sf.sveditor.core;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;

public class StringInputStream extends InputStream {
	private StringReader			fReader;
	
	public StringInputStream(String content) {
		fReader = new StringReader(content);
	}

	@Override
	public int read() throws IOException {
		return fReader.read();
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
}
