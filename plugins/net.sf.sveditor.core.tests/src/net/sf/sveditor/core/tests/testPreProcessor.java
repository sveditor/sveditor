package net.sf.sveditor.core.tests;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFilesystemIndex;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class testPreProcessor implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		/*
		SVDBFilesystemIndex ovm = new SVDBFilesystemIndex(
				new File("/tools/ovm/ovm-2.0.1/src"), ISVDBIndex.IT_BuildPath);
		 */
		SVDBFilesystemIndex ovm = new SVDBFilesystemIndex(
				new File("/usr1/fun/sveditor/uart_ovm_testbench_trunk"),
				ISVDBIndex.IT_BuildPath);
		// String filename = "/tools/ovm/ovm-2.0.1/src/base/ovm_factory.sv";
		String filename = "/usr1/fun/sveditor/uart_ovm_testbench_trunk/inFact/uart_iVCs_ovm/uart_scenario_generator/uart_scenario_generator.svh";
		
		// ovm.getFileTree();
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider();

		Map<File, SVDBFile> pp_map = ovm.getPreProcFileMap();
		
		SVDBFile scen_gen = pp_map.get(new File(filename));
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
		
		System.out.println("--> createFileContext()");
		SVDBFileTree scen_gen_ctxt = ft_utils.createFileContext(scen_gen, pp_map);
		System.out.println("<-- createFileContext()");
		
		/*
		System.out.println("--> getFileTree");
		Map<File, SVDBFileTree> tree_map = ovm.getFileTree();
		System.out.println("<-- getFileTree");
		 */
		
		dp.setFileContext(scen_gen_ctxt);
		
		SVPreProcScanner sc = new SVPreProcScanner();
		sc.setExpandMacros(true);
		sc.setDefineProvider(dp);
		
		long start = System.currentTimeMillis();
		System.out.println("--> Scanning");
		try {
			InputStream in = new FileInputStream(filename);
			sc.init(in, filename);
			
			int ch;
			do {
				if ((ch = sc.get_ch()) != -1) {
					System.out.print((char)ch);
				}
			} while (ch != -1);
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.out.println("<-- Scanning");

		long end = System.currentTimeMillis();

		System.out.println("total: " + (end-start));
		// TODO Auto-generated method stub
		return 0;
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}
