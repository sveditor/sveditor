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


package net.sf.sveditor.core.tests.indent;

import java.io.ByteArrayOutputStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class IndentTests extends TestCase {
	
	public void testBasics() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		ByteArrayOutputStream bos;
		
		LogFactory.getDefault().addLogListener(new ILogListener() {
			
			public void message(ILogHandle handle, int type, int level, String message) {
				System.out.println("[" + handle.getName() + "] " + message);
			}
		});
		
		bos = utils.readBundleFile("/data/basic_content_assist_project/class1.svh");
		
		StringBuilder sb = new StringBuilder(bos.toString());
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(sb));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		String result = indenter.indent(-1, -1);
		
		System.out.println("Result: \"" + result + "\"");
	}

}
