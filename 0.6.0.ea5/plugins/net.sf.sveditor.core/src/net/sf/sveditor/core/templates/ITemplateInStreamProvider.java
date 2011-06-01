package net.sf.sveditor.core.templates;

import java.io.InputStream;

public interface ITemplateInStreamProvider {
	
	InputStream openStream(String path);
	
	void closeStream(InputStream in);

}
