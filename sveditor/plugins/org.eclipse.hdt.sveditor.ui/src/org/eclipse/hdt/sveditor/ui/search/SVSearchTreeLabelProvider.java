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


package org.eclipse.hdt.sveditor.ui.search;

import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

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
