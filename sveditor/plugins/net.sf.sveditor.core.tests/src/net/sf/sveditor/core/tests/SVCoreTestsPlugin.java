/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

import net.sf.sveditor.core.SVCorePlugin;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCoreTestsPlugin extends Plugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core.tests";
	
	public static final String OVM_LIBRARY_ID = "org.ovmworld.ovm";
	public static final String VMM_LIBRARY_ID = "org.vmmcentral.vmm";

	// The shared instance
	private static SVCoreTestsPlugin    plugin;
	
	/**
	 * The constructor
	 */
	public SVCoreTestsPlugin() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		SVCorePlugin.setTestMode();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}
	
	public static InputStream openFile(String path) {
		SVCoreTestsPlugin p = getDefault();
		URL url = p.getBundle().getEntry(path);
		InputStream in = null;
		
		if (url != null) {
			try {
				in = url.openStream();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		return in;
	}
	
	public static String readStream(InputStream in) throws IOException {
		StringBuilder ret = new StringBuilder();
		int ch;
		
		while ((ch = in.read()) != -1) {
			ret.append((char)ch);
		}
		
		return ret.toString();
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static SVCoreTestsPlugin getDefault() {
		return plugin;
	}
	

}
