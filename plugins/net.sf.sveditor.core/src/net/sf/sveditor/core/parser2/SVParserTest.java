package net.sf.sveditor.core.parser2;

import java.io.FileInputStream;

public class SVParserTest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		SVParser p = null;
		
		for (String file : args) {
			try {
				FileInputStream in = new FileInputStream(file);
				PreprocCharStream s = new PreprocCharStream(in);
				p = new SVParser(s);
				
				p.description();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

}
