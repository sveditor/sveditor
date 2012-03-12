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


package net.sf.sveditor.ui.editor;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

public class SVColorManager {
	
	private static Map<RGB, Color>		fColorMap = new HashMap<RGB, Color>();
	
	
	public static synchronized Color getColor(RGB color) {
		Color ret = fColorMap.get(color);
		
		if (ret == null) {
			ret = new Color(Display.getDefault(), color);
			fColorMap.put(color, ret);
		}
		
		return ret;
	}
	
	public static synchronized void clear() {
		fColorMap.clear();
	}
	
	public static synchronized void dispose() {
		for (Color color : fColorMap.values()) {
			color.dispose();
		}
		fColorMap.clear();
	}
}
