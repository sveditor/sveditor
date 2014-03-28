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


package net.sf.sveditor.ui.search;

import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.StyledString;

public class SVSearchTreeLabelProvider extends SVTreeLabelProvider {
	
	public SVSearchTreeLabelProvider() {
		fShowFunctionRetType = false;
	}

	public StyledString getStyledText(Object element) {
		// TODO Auto-generated method stub
		return super.getStyledText(element);
	}
}
