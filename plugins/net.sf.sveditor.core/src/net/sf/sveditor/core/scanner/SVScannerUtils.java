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


package net.sf.sveditor.core.scanner;

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
