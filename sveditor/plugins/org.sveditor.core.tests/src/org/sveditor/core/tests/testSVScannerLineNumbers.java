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


package org.sveditor.core.tests;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.ISVDBFileFactory;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.parser.SVLanguageLevel;

public class testSVScannerLineNumbers implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		// InputStream in = Activator.openFile("data/ovm_tlm/ovm_ports.svh");
		InputStream in = SVCoreTestsPlugin.openFile("data/tlm_imps.svh");
		
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile f =  factory.parse(SVLanguageLevel.SystemVerilog, in, "tlm_imps.svh", markers);
		
		for (ISVDBItemBase it : f.getChildren()) {
			System.out.println("item \"" + SVDBItem.getName(it) + "\" @ line " + 
					SVDBLocation.unpackLineno(it.getLocation()));
		}
		
		return 0;
	}

	public void stop() {}
}
