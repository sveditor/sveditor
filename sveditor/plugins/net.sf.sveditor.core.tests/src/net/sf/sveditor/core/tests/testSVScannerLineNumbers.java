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

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.parser.SVLanguageLevel;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class testSVScannerLineNumbers implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		// InputStream in = Activator.openFile("data/ovm_tlm/ovm_ports.svh");
		InputStream in = SVCoreTestsPlugin.openFile("data/tlm_imps.svh");
		
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile f =  factory.parse(SVLanguageLevel.SystemVerilog, in, "tlm_imps.svh", markers);
		
		for (ISVDBItemBase it : f.getChildren()) {
			System.out.println("item \"" + SVDBItem.getName(it) + "\" @ line " + it.getLocation().getLine());
		}
		
		return 0;
	}

	public void stop() {}
}
