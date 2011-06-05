package net.sf.sveditor.core.templates;

import java.io.OutputStream;

public interface ITemplateOutStreamProvider {
	
	OutputStream openStream(String path);
	
	void closeStream(OutputStream out);

}
