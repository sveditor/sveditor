package net.sf.sveditor.core.tests.indent;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;

public class IndentComparator {
	
	public static void compare(String msg, String expected, String result) {
		List<String> lines_expected = split(expected);
		List<String> lines_result   = split(result);
		int lineno = 1;
		StringBuilder exp_sb = new StringBuilder();
		StringBuilder res_sb = new StringBuilder();
		int failures = 0;
		
		for (int i=0; i<lines_expected.size() && i<lines_result.size(); i++) {
			String e = (i<lines_expected.size())?lines_expected.get(i):null;
			String r = (i<lines_result.size())?lines_result.get(i):null;
			if (e != null && r != null) {
				if (e.equals(r)) {
					System.out.println(lineno + " [OK]  \"" + r + "\"");
				} else {
					System.out.println(lineno + " [ERR] expected: \"" + e + "\"");
					System.out.println(lineno + " [ERR] result  : \"" + r + "\"");
					failures++;
				}
			} else {
				System.out.println(lineno + " [ERR] expected: \"" + e + "\"");
				System.out.println(lineno + " [ERR] result  : \"" + r + "\"");
				failures++;
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
