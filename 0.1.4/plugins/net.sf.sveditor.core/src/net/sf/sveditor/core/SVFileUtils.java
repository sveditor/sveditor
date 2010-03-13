package net.sf.sveditor.core;

import java.io.File;
import java.util.regex.Pattern;

public class SVFileUtils {
	private static Pattern					fWinPathPattern;
	
	static {
		fWinPathPattern = Pattern.compile("\\\\");
	}
	
	
	public static String getPathParent(String path) {
		path = new File(path).getParent();
		return fWinPathPattern.matcher(path).replaceAll("/");
	}
	
	public static String normalize(String path) {
		return fWinPathPattern.matcher(path).replaceAll("/");
	}
	

}
