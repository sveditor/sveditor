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


package org.sveditor.core.tests.indent;

import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;

import junit.framework.TestCase;

public class IndentComparator {
	
	public static void compare(String msg, String expected, String result) {
		LogHandle log = LogFactory.getLogHandle(msg);
		compare(log, msg, expected, result);
		LogFactory.removeLogHandle(log);
	}
	
	public static void compare(LogHandle log, String msg, String expected, String result) {
		List<String> lines_expected = split(expected);
		List<String> lines_result   = split(result);
		int lineno = 1;
		StringBuilder exp_sb = new StringBuilder();
		StringBuilder res_sb = new StringBuilder();
		int failures = 0;
		
		int i;
		for (i=0; i<lines_expected.size() || i<lines_result.size(); i++) {
			String e = (i<lines_expected.size())?lines_expected.get(i):null;
			String r = (i<lines_result.size())?lines_result.get(i):null;
			if (e != null && r != null) {
				if (e.equals(r)) {
					log.debug(lineno + " [OK]  \"" + r + "\"");
				} else {
					log.debug(lineno + " [ERR] expected: \"" + e + "\"");
					log.debug(lineno + " [ERR] result  : \"" + r + "\"");
					failures++;
				}
			} else {
				if (e == null && r.equals("")) {
					log.debug(lineno + " [OK]  \"" + r + "\" [Exp==null]");
				} else if (r == null && e.equals("")) {
					log.debug(lineno + " [OK]  \"" + e + "\" [Res==null]");
				} else {
					log.debug(lineno + " [ERR] expected: \"" + e + "\"");
					log.debug(lineno + " [ERR] result  : \"" + r + "\"");
					failures++;
				}
			}
			lineno++;
		}
		
		for (String e : lines_expected) {
			exp_sb.append(e);
			exp_sb.append("\n");
		}
		for (String r : lines_result) {
			res_sb.append(r);
			res_sb.append("\n");
		}
		
//		TestCase.assertEquals(msg, exp_sb.toString(), res_sb.toString());
		TestCase.assertEquals(msg, 0, failures);
	}
	
	private static List<String> split(String input) {
		List<String> ret = new ArrayList<String>();
		StringBuilder sb = new StringBuilder();
		boolean all_ws;
		int idx = 0;
		
		while (idx < input.length()) {
			sb.setLength(0);
			all_ws = true;
			
			while (idx < input.length() && input.charAt(idx) != '\n') {
				if (!Character.isWhitespace(input.charAt(idx))) {
					all_ws = false;
				}
				sb.append(input.charAt(idx));
				idx++;
			}

			if (sb.length() > 0 || input.charAt(idx) == '\n') {
				if (all_ws) {
					ret.add("");
				} else {
					ret.add(sb.toString());
				}
			}

			if (idx >= input.length()) {
				break;
			} else {
				idx++;
			}
		}
		
		return ret;
	}
}
