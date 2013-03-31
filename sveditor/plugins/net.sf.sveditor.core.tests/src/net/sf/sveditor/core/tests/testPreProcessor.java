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

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.SVPreProcDirectiveScanner;
import net.sf.sveditor.core.scanner.FileContextSearchMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class testPreProcessor implements IApplication {

	public Object start(IApplicationContext context) throws Exception {
		LogHandle log = LogFactory.getLogHandle("testPreProcessor");
		/*
		SVDBFilesystemIndex ovm = new SVDBFilesystemIndex(
				new File("/tools/ovm/ovm-2.0.1/src"), ISVDBIndex.IT_BuildPath);
		 */
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"/usr1/fun/sveditor", SVDBSourceCollectionIndexFactory.TYPE, null);
		
		String filename = "/tools/ovm/ovm-2.0.1/src/base/ovm_factory.sv";
		
		// ovm.getFileTree();
		
		FileContextSearchMacroProvider mp = new FileContextSearchMacroProvider(null, null);
		SVPreProcDefineProvider dp = new SVPreProcDefineProvider(mp);

		// ??
		index.findPreProcFile(filename);
		
		log.debug("--> createFileContext()");
		// TODO: need to provide IncludeProvider
		SVDBFileTree scen_gen_ctxt = null; // ft_utils.createFileContext(scen_gen, null); 
		log.debug("<-- createFileContext()");
		
		mp.setFileContext(scen_gen_ctxt);
		
		SVPreProcDirectiveScanner sc = new SVPreProcDirectiveScanner();
		
		long start = System.currentTimeMillis();
		log.debug("--> Scanning");
		StringBuilder tmp = new StringBuilder();
		try {
			InputStream in = new FileInputStream(filename);
			sc.init(in, filename);
			
			int ch;
			do {
				if ((ch = sc.get_ch()) != -1) {
					tmp.append((char)ch);
				}
			} while (ch != -1);
		} catch (IOException e) {
			e.printStackTrace();
		}
		log.debug(tmp.toString());
		log.debug("<-- Scanning");

		long end = System.currentTimeMillis();

		System.out.println("total: " + (end-start));
		// TODO Auto-generated method stub
		return 0;
	}

	public void stop() {
		// TODO Auto-generated method stub

	}

}
