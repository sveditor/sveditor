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


package net.sf.sveditor.core.tests.index;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestBuiltinIndex extends SVCoreTestCaseBase {
	
	@Override
	protected void tearDown() throws Exception {
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
		
		super.tearDown();
	}

	public void testBuiltinIndexNoErrors() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBIndexCollection index_mgr = new SVDBIndexCollection("GLOBAL");
		index_mgr.addPluginLibrary(SVCorePlugin.getDefault().getBuiltinLib());
		
		IndexTestUtils.assertNoErrWarn(fLog, index_mgr);
		IndexTestUtils.assertFileHasElements(fLog, index_mgr, 
				"string", "process", "__sv_builtin_covergroup", "$finish");
	}

}
