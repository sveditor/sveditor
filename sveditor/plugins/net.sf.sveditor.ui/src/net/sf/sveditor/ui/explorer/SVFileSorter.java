/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.explorer;

import java.text.Collator;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;

public class SVFileSorter extends ViewerSorter {

	public SVFileSorter() {
		// TODO Auto-generated constructor stub
	}

	public SVFileSorter(Collator collator) {
		super(collator);
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		if (e1 instanceof ISVDBChildItem && e2 instanceof ISVDBChildItem) {
			ISVDBChildItem p1 = ((ISVDBChildItem)e1).getParent();
			ISVDBChildItem p2 = ((ISVDBChildItem)e2).getParent();
			
			if (p1 != p2) {
				System.out.println("parents are not equal");
			}
		
			int i1 = ((ISVDBScopeItem)p1).getItems().indexOf(e1);
			int i2 = ((ISVDBScopeItem)p2).getItems().indexOf(e2);
			
			return (i1 - i2);
		}
		return super.compare(viewer, e1, e2);
	}

	@Override
	public void sort(Viewer viewer, Object[] elements) {
		System.out.println("SVFileSorter.sort()");
	}
}
