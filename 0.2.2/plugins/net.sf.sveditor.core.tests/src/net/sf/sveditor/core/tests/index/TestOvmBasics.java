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


package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestOvmBasics extends TestCase {
	
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
		}
	}

	public void testBasicProcessing() {
		File tmpdir = new File(fTmpDir, "no_errors");
		
		if (tmpdir.exists()) {
			tmpdir.delete();
		}
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(tmpdir);
	
		SVDBIndexCollectionMgr index_mgr = new SVDBIndexCollectionMgr("GLOBAL");
		index_mgr.addPluginLibrary(
				rgy.findCreateIndex("GLOBAL", "org.ovmworld.ovm", 
						SVDBPluginLibIndexFactory.TYPE, null));
		
		ISVDBItemIterator<SVDBItem> index_it = index_mgr.getItemIterator();
		List<SVDBMarkerItem> markers = new ArrayList<SVDBMarkerItem>();
		SVDBItem ovm_component=null;
		SVDBItem ovm_sequence=null;
		
		while (index_it.hasNext()) {
			SVDBItem it = index_it.nextItem();
			System.out.println("" + it.getType() + " " + it.getName());
			
			if (it.getType() == SVDBItemType.Marker) {
				markers.add((SVDBMarkerItem)it);
			} else if (it.getType() == SVDBItemType.Class) {
				if (it.getName().equals("ovm_component")) {
					ovm_component = it;
				} else if (it.getName().equals("ovm_sequence")) {
					ovm_sequence = it;
				}
			} else if (it.getType() == SVDBItemType.Macro) {
			} else if (it.getType() == SVDBItemType.VarDecl) {
				SVDBVarDeclItem v = (SVDBVarDeclItem)it;
				
				assertNotNull("Variable " + it.getParent().getName() + "." +
						it.getName() + " has a null TypeInfo", v.getTypeInfo());
			}
		}
		
		assertEquals("Check that no errors were found", 0, markers.size());
		assertNotNull("Check found ovm_sequence", ovm_sequence);
		assertNotNull("Check found ovm_component", ovm_component);
	}

}
