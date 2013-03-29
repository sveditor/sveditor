package net.sf.sveditor.core.tests.argcollector;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SystemOutLineListener;
import net.sf.sveditor.core.argcollector.ArgCollectorFactory;
import net.sf.sveditor.core.argcollector.IArgCollector;
import net.sf.sveditor.core.argfile.filter.ArgFileFilterCppFiles;
import net.sf.sveditor.core.argfile.filter.ArgFileFilterList;
import net.sf.sveditor.core.argfile.filter.ArgFileWriter;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;

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
