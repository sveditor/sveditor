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


package net.sf.sveditor.core.tests;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;

public class SVDBIndexProfiler {
	
	
	public static final void main(String args[]) {
		// File root = new File(args[0]);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		/* ISVDBIndex index = */ rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", args[0], SVDBSourceCollectionIndexFactory.TYPE, null);
		
		try {
			Thread.sleep(30000);
		} catch (Exception e) { } 
	}
}
