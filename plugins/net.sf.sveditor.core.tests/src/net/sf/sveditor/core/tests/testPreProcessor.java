package net.sf.sveditor.core.tests;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

import net.sf.sveditor.core.ISVDBIndex;
import net.sf.sveditor.core.SVDBFilesystemIndex;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class testPreProcessor implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		SVDBFilesystemIndex ovm = new SVDBFilesystemIndex(
				new File("/tools/ovm/ovm-2.0.1/src"), ISVDBIndex.IT_BuildPath, null);
		String filename = "/tools/ovm/ovm-2.0.1/src/tlm/ovm_ports.svh";
		
		ovm.getFileTree();
		
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(ovm);
		
		System.out.println("--> getFileTree");
		Map<File, SVDBFileTree> tree_map = ovm.getFileTree();
		System.out.println("<-- getFileTree");
		
		dp.setFileContext(tree_map.get(new File(filename)));
		
		
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
					// System.out.print((char)ch);
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
