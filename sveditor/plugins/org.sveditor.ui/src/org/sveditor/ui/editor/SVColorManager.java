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


package org.sveditor.ui.editor;

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
