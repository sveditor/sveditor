package net.sf.sveditor.core.templates;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

import org.osgi.framework.Bundle;

public class PluginInStreamProvider implements ITemplateInStreamProvider {
	Bundle				fBundle;
	
	public PluginInStreamProvider(Bundle bundle) {
		fBundle = bundle;
	}

	public InputStream openStream(String path) {
		URL url = fBundle.getEntry(path);
		InputStream in = null;
		
		if (url != null) {
			try {
				in = url.openStream();
			} catch (IOException e) {}
		}
		
		return in;
	}

	public void closeStream(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}

}
