/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.ui.explorer;

import org.eclipse.hdt.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DecoratingLabelProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PlatformUI;

public class SVExplorerDecoratingLabelProvider extends DecoratingLabelProvider {
	
	public SVExplorerDecoratingLabelProvider() {
		super(new SVTreeLabelProvider(),
			PlatformUI.getWorkbench().getDecoratorManager().getLabelDecorator());
	}

	@Override
	public Image getImage(Object element) {
		return super.getImage(element);
	}

	@Override
	public ILabelProvider getLabelProvider() {
		// TODO Auto-generated method stub
		return super.getLabelProvider();
	}
	
}
