package net.sf.sveditor.svt.core.templates;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

public class FSInStreamProvider implements ITemplateInStreamProvider {

	public InputStream openStream(String path) {
		File file = new File(path);
		InputStream in = null;
		
		try {
			in = new FileInputStream(file);
		} catch (IOException e) {}
		
		return in;
	}

	public void closeStream(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}

}
