package net.sf.sveditor.core.db.index;

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
			} catch (IOException e) {}
		}

		return new ByteArrayInputStream(fOut.toByteArray());
	}

}
