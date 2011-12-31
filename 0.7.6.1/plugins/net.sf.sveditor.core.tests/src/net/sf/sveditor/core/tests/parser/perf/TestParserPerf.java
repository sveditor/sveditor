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


package net.sf.sveditor.core.tests.parser.perf;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestParserPerf extends TestCase {

	public void testXBusExample() {
		/*
		LogFactory.getDefault().addLogListener(new ILogListener() {
			
			public void message(ILogHandle handle, int type, int level, String message) {
				System.out.println("[MSG] " + message);
			}
		});
		 */
		
		String cls_path = "net/sf/sveditor/core/tests/CoreReleaseTests.class";
		URL plugin_class = getClass().getClassLoader().getResource(cls_path);
		System.out.println("plugin_class: " + plugin_class.toExternalForm());
		String path = plugin_class.toExternalForm();
		path = path.substring("file:".length());
		path = path.substring(0, path.length()-(cls_path.length()+"/class/".length()));
		
		String ovm_dir = path + "/ovm";

//		SVCorePlugin.getDefault().enableDebug(false);
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		String xbus = ovm_dir + "/examples/xbus";

		SVDBIndexRegistry rgy = new SVDBIndexRegistry(true);
		SVDBArgFileIndexFactory factory = new SVDBArgFileIndexFactory();
		rgy.test_init(TestIndexCacheFactory.instance(null));
		
		String compile_questa_sv = xbus + "/examples/compile_questa_sv.f";
		System.out.println("compile_questa_sv=" + compile_questa_sv);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				compile_questa_sv, SVDBArgFileIndexFactory.TYPE, factory, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarker m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
	}

}
