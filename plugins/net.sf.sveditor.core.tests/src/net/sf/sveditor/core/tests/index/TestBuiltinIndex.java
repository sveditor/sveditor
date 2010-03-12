package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestBuiltinIndex extends TestCase {
	File					fTmpDir;
	
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

	public void testBuiltinIndexNoErrors() {
		File tmpdir = new File(fTmpDir, "no_errors");
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		if (tmpdir.exists()) {
			tmpdir.delete();
		}
		tmpdir.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(tmpdir);
	
		SVDBIndexCollectionMgr index_mgr = new SVDBIndexCollectionMgr("GLOBAL");
		index_mgr.addPluginLibrary(
				rgy.findCreateIndex("GLOBAL", SVCorePlugin.SV_BUILTIN_LIBRARY, 
						SVDBPluginLibIndexFactory.TYPE, null));
		
		ISVDBItemIterator<SVDBItem> index_it = index_mgr.getItemIterator();
		List<SVDBMarkerItem> markers = new ArrayList<SVDBMarkerItem>();
		SVDBItem string_cls=null, process_cls=null, covergrp_cls=null;
		SVDBItem finish_task=null;
		
		while (index_it.hasNext()) {
			SVDBItem it = index_it.nextItem();
			
			if (it.getType() == SVDBItemType.Marker) {
				markers.add((SVDBMarkerItem)it);
			} else if (it.getType() == SVDBItemType.Class) {
				if (it.getName().equals("string")) {
					string_cls = it;
				} else if (it.getName().equals("process")) {
					process_cls = it;
				} else if (it.getName().equals("__sv_builtin_covergroup")) {
					covergrp_cls = it;
				}
			} else if (it.getType() == SVDBItemType.Task) {
				if (it.getName().equals("$finish")) {
					finish_task = it;
				}
			}
		}
		
		assertEquals("Check that no errors were found", 0, markers.size());
		assertNotNull("Check found string", string_cls);
		assertNotNull("Check found process", process_cls);
		assertNotNull("Check found covergroup", covergrp_cls);
		assertNotNull("Check found $finish", finish_task);
	}

}
