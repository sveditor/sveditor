/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.doc.user;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

public class Activator extends Plugin {
	
	private static Activator				fPlugin;

	@Override
	public void start(BundleContext context) throws Exception {

		super.start(context);
		fPlugin = this;
	}

	@Override
	public void stop(BundleContext context) throws Exception {

		fPlugin = null;
		super.stop(context);
	}
	
	
	public static Activator getDefault() {
		return fPlugin;
	}
	

}
