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


package net.sf.sveditor.core.tests;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFileTreeUtils;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.src_collection.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
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
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", "/usr1/fun/sveditor",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		String filename = "/tools/ovm/ovm-2.0.1/src/base/ovm_factory.sv";
		
		// ovm.getFileTree();
		
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider();
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);

		Map<String, SVDBFile> pp_map = index.getPreProcFileMap();
		
		SVDBFile scen_gen = pp_map.get(new File(filename));
		SVDBFileTreeUtils ft_utils = new SVDBFileTreeUtils();
		
		System.out.println("--> createFileContext()");
		// TODO: need to provide IncludeProvider
		SVDBFileTree scen_gen_ctxt = ft_utils.createFileContext(scen_gen, null); 
		System.out.println("<-- createFileContext()");
		
		/*
		System.out.println("--> getFileTree");
		Map<File, SVDBFileTree> tree_map = ovm.getFileTree();
		System.out.println("<-- getFileTree");
		 */
		
		mp.setFileContext(scen_gen_ctxt);
		
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
