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

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class IndentTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("IndentTests");
		suite.addTest(new TestSuite(IndentTests.class));
		suite.addTest(new TestSuite(NoHangIndentTests.class));
		
		return suite;
	}
	
	public void testBasics() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		ByteArrayOutputStream bos;
		
		// SVCorePlugin.getDefault().enableDebug(true);
		
		bos = utils.readBundleFile("/indent/class1.svh");
		
		String ref = bos.toString();
		StringBuilder sb = new StringBuilder();
		
		int i=0;
		
		while (i < ref.length()) {
			// Read leading whitespace
			while (i < ref.length() && 
					Character.isWhitespace(ref.charAt(i)) &&
					ref.charAt(i) != '\n') {
				i++;
			}
			
			if (i >= ref.length()) {
				break;
			}
			
			if (ref.charAt(i) == '\n') {
				sb.append('\n');
				i++;
				continue;
			} else {
				// Read to the end of the line
				while (i < ref.length() && ref.charAt(i) != '\n') {
					sb.append(ref.charAt(i));
					i++;
				}
				
				if (i < ref.charAt(i)) {
					sb.append('\n');
				}
			}
		}

		// Run the indenter over the reference source
		SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(sb));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		
		StringBuilder result = new StringBuilder(indenter.indent(-1, -1));
		StringBuilder reference = new StringBuilder(ref);
		
		String ref_line, ind_line;
		int err_cnt = 0;
		int pass_cnt = 0;
		
		do {
			ref_line = readLine(reference);
			ind_line = readLine(result);
			
			if (ref_line != null && ind_line != null) {
				if (ref_line.equals(ind_line)) {
					System.out.println("[OK ]:" + ref_line);
					pass_cnt++;
				} else {
					System.out.println("[ERR]:" + ref_line);
					System.out.println("[   ]:" + ind_line);
					err_cnt++;
				}
			}
		} while (ref_line != null && ind_line != null);
		
		assertNull("Checking that output not truncated", ref_line);
		assertNull("Checking for no excess output", ind_line);
		
		assertEquals("Expect no errors", 0, err_cnt);
		assertTrue("Check accomplished work", (pass_cnt != 0));
	}
	
	private String readLine(StringBuilder sb) {
		int end = 0;
		String ret = null;
		
		while (end < sb.length() && sb.charAt(end) != '\n') {
			end++;
		}
		
		if (end < sb.length()) {
			if (end == 0) {
				ret = "";
				sb.delete(0, 1);
			} else {
				ret = sb.substring(0, end);
				sb.delete(0, end+1);
			}
		}
		
		return ret;
	}

}
