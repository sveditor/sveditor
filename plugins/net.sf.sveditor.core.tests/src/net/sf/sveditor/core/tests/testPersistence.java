/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.persistence.SVDBDump;
import net.sf.sveditor.core.db.persistence.SVDBLoad;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

public class testPersistence implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		/*
		SVDBFilesystemIndex ovm = new SVDBFilesystemIndex(
				new File("/tools/ovm/ovm-2.0.1/src"), ISVDBIndex.IT_BuildPath);
		 */
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(
				"foo", "net.sf.sveditor.ovm_2.0.1", 
				SVDBPluginLibIndexFactory.TYPE, null);
		
		index.getFileDB();
		
		SVDBDump dump = new SVDBDump();
		
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		dump.dump(index, bos);
		

		SVDBLoad load = new SVDBLoad();
		
		Map<String, SVDBFile> pp_map = new HashMap<String, SVDBFile>();
		Map<String, SVDBFile> db_map = new HashMap<String, SVDBFile>();
		load.load(pp_map, db_map, new ByteArrayInputStream(bos.toByteArray()));
		
		return 0;
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}
