/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;

import java.util.Iterator;

public class SVDBUtil {
	
	public static int getChildrenSize(ISVDBChildParent p) {
		int count=0;
		Iterator<ISVDBChildItem> it = p.getChildren().iterator();
		while (it.hasNext()) {
			count++;
			it.next();
		}
		return count;
	}
	
	public static ISVDBChildItem getFirstChildItem(ISVDBChildParent p) {
		Iterator<ISVDBChildItem> it = p.getChildren().iterator();
		if (it.hasNext()) {
			return it.next();
		} else {
			return null;
		}
	}
	
	public static void addAllChildren(ISVDBChildParent dest, ISVDBChildParent src) {
		for (ISVDBChildItem c : src.getChildren()) {
			dest.addChildItem(c);
		}
	}

}
