package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

public class SVScannerUtils {
	
	
	public static List<String> splitCommaSepString(String list) {
		List<String> ret = new ArrayList<String>();
		
		String sep[] = list.split(",");
		
		for (String el : sep) {
			el = el.trim();
			
			if (el.length() > 0) {
				ret.add(el);
			}
		}
		
		return ret;
	}

}
