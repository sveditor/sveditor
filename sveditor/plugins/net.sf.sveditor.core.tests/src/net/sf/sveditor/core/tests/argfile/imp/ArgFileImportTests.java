/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.argfile.imp;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.argcollector.BaseArgCollector;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;

public class ArgFileImportTests extends SVCoreTestCaseBase {
	
	public void testBasicUBusImport() throws IOException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		BaseArgCollector collector = new BaseArgCollector(); 
		
		utils.unpackBundleZipToFS("uvm.zip", fTmpDir);

		File ubus_examples = new File(fTmpDir, 
				"uvm/examples/integrated/ubus/examples");
		List<String> cmdline = new ArrayList<String>();
		cmdline.add("make");
		cmdline.add("-f");
		cmdline.add("Makefile.questa");
		cmdline.add("alt");
		
		collector.process(ubus_examples, cmdline);
		
		String arguments = collector.getArguments();
		
		System.out.println("arguments=" + arguments);
	}
	

}
