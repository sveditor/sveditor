package net.sf.sveditor.ui.editor;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

public enum SVEditorColors {
	DEFAULT,
	KEYWORD,
	STRING,
	SINGLE_LINE_COMMENT,
	MULTI_LINE_COMMENT;

	private static Map<SVEditorColors, RGB>			fColorMap;
	private static Map<SVEditorColors, Integer>		fStyleMap;
	
	static {
		fColorMap = new HashMap<SVEditorColors, RGB>();
		fStyleMap = new HashMap<SVEditorColors, Integer>();
		
		fColorMap.put(DEFAULT, new RGB(0, 0, 0));
		fColorMap.put(STRING, new RGB(42, 0, 255));
		fColorMap.put(SINGLE_LINE_COMMENT, new RGB(0, 128, 0));
		fColorMap.put(MULTI_LINE_COMMENT, new RGB(0, 128, 0));
		
		fColorMap.put(KEYWORD, new RGB(128, 0, 64));
		fStyleMap.put(KEYWORD, SWT.BOLD);
	}
	
	public static Color getColor(SVEditorColors color) {
		return SVColorManager.getColor(fColorMap.get(color));
	}
	
	public static int getStyle(SVEditorColors color) {
		if (fStyleMap.containsKey(color)) {
			return fStyleMap.get(color);
		} else {
			return SWT.NORMAL;
		}
	}
}
