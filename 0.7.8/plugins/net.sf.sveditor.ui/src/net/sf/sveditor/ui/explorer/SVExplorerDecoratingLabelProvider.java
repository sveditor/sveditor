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


package net.sf.sveditor.ui.explorer;

import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.jface.viewers.DecoratingLabelProvider;
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

	
	
}
