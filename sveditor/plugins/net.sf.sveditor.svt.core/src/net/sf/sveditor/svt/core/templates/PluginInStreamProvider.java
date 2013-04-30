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


package net.sf.sveditor.svt.core.templates;

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
