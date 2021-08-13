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
package org.eclipse.hdt.sveditor.core.tests.argcollector;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SystemOutLineListener;
import org.eclipse.hdt.sveditor.core.argcollector.ArgCollectorFactory;
import org.eclipse.hdt.sveditor.core.argcollector.IArgCollector;
import org.eclipse.hdt.sveditor.core.argfile.filter.ArgFileFilterCppFiles;
import org.eclipse.hdt.sveditor.core.argfile.filter.ArgFileFilterList;
import org.eclipse.hdt.sveditor.core.argfile.filter.ArgFileWriter;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileLexer;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileParser;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;

public class TestArgCollectorBasics extends SVCoreTestCaseBase {
	
	public void testUvmUbus() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		IArgCollector collector = ArgCollectorFactory.create();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);

		File ubus_examples = new File(fTmpDir, "uvm/examples/integrated/ubus/examples");
		List<String> args = new ArrayList<String>();
		
		args.add("make");
		args.add("-f");
		// VCS makefile doesn't require DPI library to be compiled
		args.add("Makefile.questa");
		args.add("alt");
	
		collector.addStderrListener(new SystemOutLineListener());
		collector.addStdoutListener(new SystemOutLineListener());

		collector.process(ubus_examples, args);
	
		String arguments = collector.getArguments();
	
		SVArgFileParser parser = new SVArgFileParser(
				ubus_examples.getAbsolutePath(),
				ubus_examples.getAbsolutePath(),
				new SVDBFSFileSystemProvider());
		SVArgFileLexer lexer = new SVArgFileLexer();
		lexer.init(null, new StringTextScanner(arguments));
		parser.init(lexer, "");
		
		SVDBFile argfile = new SVDBFile("");
		
		try {
			parser.parse(argfile, new ArrayList<SVDBMarker>());
		} catch (SVParseException e) {
			e.printStackTrace();
		}
		
		ArgFileFilterList filters = new ArgFileFilterList();
		filters.addFilter(new ArgFileFilterCppFiles());
		
		argfile = filters.filter(argfile);
		
		ArgFileWriter writer = new ArgFileWriter();
		System.out.println("Arguments: " + arguments);
	
		System.out.println("Filtered:");
		writer.write(argfile, System.out);
		
	}

}
