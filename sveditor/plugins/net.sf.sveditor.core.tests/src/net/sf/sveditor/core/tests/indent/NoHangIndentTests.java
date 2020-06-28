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


package net.sf.sveditor.core.tests.indent;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;

import junit.framework.TestCase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.indent.ISVIndenter;
import org.eclipse.hdt.sveditor.core.indent.SVIndentScanner;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;
import org.osgi.framework.Bundle;

public class NoHangIndentTests extends TestCase {
	
	/**
	 * testIndentNoHang()
	 * 
	 * Run the indenter through all the OVM source files, just to check that it
	 * doesn't hang
	 */
	@SuppressWarnings("unchecked")
	public void testIndentNoHang() {
		LogHandle log = LogFactory.getLogHandle("testIndentNoHang");
		Bundle bundle = SVCoreTestsPlugin.getDefault().getBundle();
		
		Enumeration<URL> sv_entries = (Enumeration<URL>)bundle.findEntries("ovm", "*.sv", true);
		Enumeration<URL> svh_entries = (Enumeration<URL>)bundle.findEntries("ovm", "*.svh", true);
		int passes=0, failures=0;
		
		while (sv_entries != null && sv_entries.hasMoreElements()) {
			URL url = sv_entries.nextElement();
			if (noHangTestInt(url)) {
				passes++;
			} else {
				failures++;
			}
		}
		
		while (svh_entries != null && svh_entries.hasMoreElements()) {
			URL url = svh_entries.nextElement();
			if (noHangTestInt(url)) {
				passes++;
			} else {
				failures++;
			}
		}
		log.debug("testIndentNoHang: " + passes + " pass " + failures + " fail");
		assertEquals("Check for no failures", failures, 0);
		LogFactory.removeLogHandle(log);
	}
	
	public void testSpecifySpecParamHang() {
		String doc = 
			"module a_module ( );\n" +
			"	specify\n" +
			"		specparam align     = 5         ; //\n" +
			"	endspecify\n" +
			"endmodule\n"
			;
		
		assertTrue(noHangTestInt(doc));
	}
	
	private boolean noHangTestInt(final URL url) {
		InputStream in = null;
		
		try {
			in = url.openStream();
		} catch (Exception e) {
			System.out.println("[ERROR] failed to open \"" + url.getPath() + "\"");
			return false;
		}
		
		return noHangTestInt(url.getPath(), in);
	}
	
	private boolean noHangTestInt(String in) {
		return noHangTestInt(null, new StringInputStream(in));
	}
	
	
	private boolean noHangTestInt(String name, final InputStream in) {
		boolean ret = true;
		// System.out.println("URL: " + url.getPath());
		final Object monitor = new Object();
		
		Thread t = new Thread(new Runnable() {
			public void run() {
				StringBuilder sb = new StringBuilder();
				byte data[] = new byte[4096];
				int sz;
				
				try {
					sz = in.read(data, 0, data.length);
					for (int i=0; i<sz; i++) {
						sb.append((char)data[i]);
					}
				} catch (IOException e) {}
				
				SVIndentScanner scanner = new SVIndentScanner(
						new StringBIDITextScanner(sb.toString()));
				ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
				indenter.init(scanner);
				
				indenter.indent();
				
				synchronized (monitor) {
					monitor.notify();
				}
			}
		});
		t.start();
		
		try {
			t.join(2000);
			
			if (t.isAlive()) {
				if (name != null) {
					System.out.println("FAILED: on file \"" + name + "\"");
				}
				ret = false;
				t.interrupt();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return ret;
	}
}
