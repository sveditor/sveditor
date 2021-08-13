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


package org.eclipse.hdt.sveditor.core.tests.srcgen;

import java.io.File;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

public class SrcGenTests extends TestSuite {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("SrcGenTests");
		suite.addTest(new TestSuite(TestNewClassGen.class));
		suite.addTest(new TestSuite(TestMethodGenerator.class));
		
		return suite;
	}
	
	public static ISVDBIndex createIndex(
			File 					tmpdir, 
			SVDBIndexRegistry		rgy,
			String 					doc) {
		if (!tmpdir.isDirectory()) {
			TestCase.assertTrue(tmpdir.mkdirs());
		}
		
		TestUtils.copy(
				doc,
				new File(tmpdir, "doc.sv")
				);
		
		TestUtils.copy(
				"" + tmpdir.getAbsolutePath() + "/doc.sv",
				new File(tmpdir, "doc.f")
				);
	
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), 
				tmpdir.getName(), 
				new File(tmpdir, "doc.f").getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, 
				null);
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		
		return index;
	}

}
