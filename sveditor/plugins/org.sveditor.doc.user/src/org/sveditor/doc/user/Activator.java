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


package org.sveditor.doc.user;

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
