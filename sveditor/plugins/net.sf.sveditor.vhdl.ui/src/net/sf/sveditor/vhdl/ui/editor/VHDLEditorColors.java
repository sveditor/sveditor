package net.sf.sveditor.vhdl.ui.editor;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.RGB;

public enum VHDLEditorColors {
	DEFAULT,
	KEYWORD,
	STRING,
	COMMENT;

	/*
	public static final String				DEFAULT_C   = "default_c";
	public static final String				KEYWORD_C   = "keyword_c";
	public static final String				STRING_C    = "string_c";
	public static final String				COMMENT_C   = "comment_c";

	public static final String				DEFAULT_S   = "default_s";
	public static final String				KEYWORD_S   = "keyword_s";
	public static final String				STRING_S    = "string_s";
	public static final String				COMMENT_S   = "comment_s";
	 */

	private static Map<VHDLEditorColors, RGB>              fColorMap;
	private static Map<VHDLEditorColors, Integer>          fStyleMap;

	static {
		fColorMap = new HashMap<VHDLEditorColors, RGB>();
		fStyleMap = new HashMap<VHDLEditorColors, Integer>();

		fColorMap.put(DEFAULT, new RGB(0, 0, 0));
		fColorMap.put(STRING, new RGB(0x2a, 0, 0xff)); // #2A00FF
		fColorMap.put(COMMENT, new RGB(0, 128, 0)); // #008000
		fColorMap.put(KEYWORD, new RGB(0x80, 0, 0x40)); // #800040
		
		fStyleMap.put(DEFAULT, SWT.NORMAL);
		fStyleMap.put(STRING, SWT.NORMAL);
		fStyleMap.put(COMMENT, SWT.NORMAL);
		fStyleMap.put(KEYWORD, SWT.BOLD);
	}

	public static RGB getColor(VHDLEditorColors color) {
		if (fColorMap.containsKey(color)) {
			return fColorMap.get(color);
		} else {
			return fColorMap.get(DEFAULT);
		}
	}
	
	public static int getStyle(VHDLEditorColors color) {
		if (fStyleMap.containsKey(color)) {
			return fStyleMap.get(color);
		} else {
			return SWT.NORMAL;
		}
	}
}
