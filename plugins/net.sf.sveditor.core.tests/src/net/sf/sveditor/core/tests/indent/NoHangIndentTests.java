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

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;

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
		System.out.println("testIndentNoHang: " + passes + " pass " + failures + " fail");
		assertEquals("Check for no failures", failures, 0);
	}
	
	private boolean noHangTestInt(final URL url) {
		boolean ret = true;
		// System.out.println("URL: " + url.getPath());
		InputStream in_t = null;
		final Object monitor = new Object();
		
		try {
			in_t = url.openStream();
		} catch (Exception e) {
			System.out.println("[ERROR] failed to open \"" + url.getPath() + "\"");
			return false;
		}
		
		final InputStream in = in_t;

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
				System.out.println("FAILED: on file \"" + url.getPath() + "\"");
				ret = false;
				t.interrupt();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return ret;
	}
}
