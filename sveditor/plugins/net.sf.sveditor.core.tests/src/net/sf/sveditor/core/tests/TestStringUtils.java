package net.sf.sveditor.core.tests;

public class TestStringUtils {
	
	public static int lineOfIndex(String content, int idx) {
		int line = 1;
		
		for (int i=0; i<=idx; i++) {
			int ch = content.charAt(i);
			
			if (ch == '\n') {
				line++;
			}
		}
	
		return line;
	}

}
